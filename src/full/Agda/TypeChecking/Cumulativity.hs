module Agda.TypeChecking.Cumulativity where

import Data.Maybe
import Data.List ((\\), delete, intersect, group, sort)
import Data.Traversable (Traversable)
import Data.Map (Map, (!), keys, unionWith, foldrWithKey, insert, empty)
import qualified Data.Map as Map (map,fold)
import Control.Monad

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad

import Agda.Utils.Impossible
import Control.Exception (assert)
import Agda.TypeChecking.Primitive (Lvl)
import Debug.Trace (trace)

{-# OPTIONS_GHC -ddump-simpl-stats #-}

--remove duplicates from a given list, and reorders it
remove_dups :: (Ord a) => [a] -> [a]
remove_dups = map head . group . sort


union :: (Ord k,Ord a) => Map k a -> Map k a -> Map k a
union = unionWith max 

data LvlVariable  =
      VarL {-# UNPACK #-} !Int Elims
    | MetaL {-# UNPACK #-} !MetaId Elims
    deriving (Eq, Ord,Show)

type Presentation = [(LvlVariable,Integer)]

type Horn = (Presentation,(LvlVariable , Integer))

data LevelEq = Eq Presentation Presentation

level_to_presentation :: Level -> Presentation
level_to_presentation (Max i l) =
    map (\(Plus j l) -> (to_var l,i+j)) l
    where
        to_var :: Term -> LvlVariable
        to_var (Var i es) = VarL i es
        to_var (MetaV x es) = MetaL x es
        to_var _ = __IMPOSSIBLE__

cmp_to_eq :: Comparison -> Level -> Level -> LevelEq
cmp_to_eq CmpEq a b = Eq (level_to_presentation a) (level_to_presentation b)
cmp_to_eq CmpLeq a b =
    let a' = level_to_presentation a
        b' = level_to_presentation b
    in Eq a' (a' ++ b')

to_horns :: LevelEq -> [Horn]
to_horns (Eq a b) =
    let a' = map (b,) a
        b' = map (a,) b
    in a' ++ b'

data NInf =
      Nat !Integer
    | NInf
    deriving (Eq, Show)

instance Ord NInf where
    compare (Nat i) (Nat j) = compare i j
    compare (Nat _) NInf = LT
    compare NInf (Nat _) = GT
    compare NInf NInf = EQ

gain :: Horn -> Integer
gain (clauses,(_,l)) = l - foldl (flip $ max . snd) 0 clauses

max_gain :: [Horn] -> Integer
max_gain l = foldl (flip $ max . gain) 0 l

type Model = Map LvlVariable NInf

is_satisfied_by :: Horn -> Model -> Bool
is_satisfied_by (x,(y,l)) f =
    if all (\(xi,ki) -> (Nat ki) <= f ! xi) x
    then (Nat l) <= f ! y
    else True

to_nat :: NInf -> Integer
to_nat (Nat n) = n
to_nat _ = __IMPOSSIBLE__

--lemma_3_1 :: (LvlVariable -> NInf) -> Horn -> Bool
--lemma_3_1 f (x,(y,l)) =
--    let w = filter ((/= NInf) . f. fst) x
--    in case w of
--        [] -> f y == NInf
--        _  ->
--            let k0 = minimum $ map (\(xi,ki) ->
--                    case f xi of
--                        NInf -> 0
--                        Nat n -> n - ki)
--                    x
--            in k0 < 0 || Nat (l+k0) <= f y
--
----lemma_3_3 v sc trans w f, given W is a strict subset of V,
---- and that for all f models, trans f is the least g>=f model of SC|W, and f a model such that f(v-w) \subset N, computes the least model of SCvW
--lemma_3_3 :: [LvlVariable] -> [Horn] -> (Model -> Model) -> [LvlVariable]  -> Model -> Maybe Model
--lemma_3_3 v sc trans w f = do
--    -- W \subset V strict, f : V -> NInf and f(v-w) \subset N
--    guard $ isSublistOf w v && v /= w && all ((NInf /=) . f) (v \\ w)
--    let fw      = (w,f)
--        maxgain = max_gain sc
--        -- gf = least g>=f that models SC|w
--        gf      = trans $ snd fw
--        -- Maxgain + max(f(V − W))
--        maxf_v_w = maxgain + foldl (flip $ max . to_nat . f) 0 (v \\ w)
--        -- Sum for w \in W of max(0,maxf_v_w-gf(w))
--        mgf = foldl (\acc w -> acc + (max 0 $ (maxf_v_w - (to_nat $ gf w)))) 0 w
--        base_case = Just $ \x -> if elem x w then gf x else f x
--    if (mgf == 0)
--    then base_case
--    else
--        -- List of clauses in SCvW - SC|W not satisfied by gf
--        let leftovers = filter (\(x,(y,l)) -> elem y w && any (not . (flip elem w) . fst) x) sc
--            unsat_leftovers = filter (lemma_3_1 gf) leftovers
--        in case unsat_leftovers of
--            [] ->  base_case
--            _  ->
--                let w0 = __IMPOSSIBLE__
--                in let f' = \x -> if x == w0 then __IMPOSSIBLE__
--                        else if elem x w
--                        then gf x
--                        else f x
--                in lemma_3_3 v sc trans (delete w0 w) f'
sorry :: a
sorry = __IMPOSSIBLE__

forward :: [Horn] -> Model -> ([LvlVariable],Model)
forward h f = --v unused ???????????????????????????????????
    trace ("\n  FORWARDING " ++ show h ++ " " ++ show f ++ "\n") $
    let forwarded = map forward_one h in
    let !(changed_vars,new_model) = foldl (\(vars,model) maybe  ->
            case maybe of
            Nothing -> (vars,model)
            Just (v,f) -> if f == model ! v then (vars,model) else
                (v:vars, insert v (max f (model ! v)) model)
            )    
            ([],f)
            forwarded in
    let res = (remove_dups changed_vars,new_model) in
    trace ("\n  FORWARDING RESULT " ++ show res ++ "\n") res

    where
        -- find the biggest value generated by the clauses in the upwards closure of a single Horn clause
        forward_one :: Horn -> Maybe (LvlVariable,NInf)
        forward_one (x,(v,l)) = 
            trace ("forwarding clause \n    " ++ show (x,(v,l))) $ do
            -- if the model satisfies the presentation A, return the biggest k such that A + k is also satisfied 
            to_up <- foldM 
                    (\acc (x,k)  -> 
                        let n = f ! x in
                        trace ("checking \n    " ++ show x ++ " + " ++ show k ++ "\n where \n   " ++ show x ++ " := " ++ show n) $
                        case f ! x of
                            NInf        -> Just acc
                            Nat n       -> Just $ max 0 $ min acc (n - k)
                    ) 
                    (toInteger (maxBound :: Int)) --TODO convert algorithm to use Int, or find a safe max-bound
                    x  
            trace ("to_up = " ++ show to_up) $
                case f ! v of
                    NInf -> Nothing
                    Nat n -> Just (v,Nat $ max n $ to_up + l)
            

simplify_ :: [Horn] -> Model -> Maybe ([Horn],Model)
simplify_ c f =
    let all_finite = foldr (\x b -> b && (x<NInf)) True f in
    if all_finite then Nothing else
    Just $
    foldrWithKey
        (\x k (c,h) -> if k==NInf then (remove x c,h) else (c,insert x k h))
        (c,empty)
        f

    where
        remove x = remove_many [x]

        remove_many [] t = t
        remove_many (x:xs) t =
            let t' = remove_one x t
                l = to_delete xs t in
            remove_many l t'

        remove_one x [] = []
        remove_one x ((_,(y,_)):t) | x==y = remove_one x t
        remove_one x ((l,v):t) = (filter ((==x) . fst) l,v):(remove_one x t)

        to_delete acc [] = acc
        to_delete acc (([],(v,_)):t) = to_delete (v:acc) t
        to_delete acc (_:t) = to_delete acc t

lemma33 :: [LvlVariable] -> [LvlVariable] -> [Horn] -> Model -> Model
lemma33 v w c f =
    trace ("\nLEMMA33 " ++ show v ++ " "++ show w ++ " "++ show c++ " " ++ show f++ "\n") $
    let res = let cw = filter (\(x,(y,l)) -> elem y w && all ((flip elem w) . fst) x) c
                  g = thm32 w [] cw f
                  f_or_g = union f g
                  c_down_w = filter (\(x,(y,l)) -> elem y w) c
                  (w',g') = forward c_down_w f_or_g in
              if w' == [] then
                  f_or_g
              else
                  lemma33 v w c (union f g')
    in trace ("\nLEMMA33 RESULT "++ show v ++ " " ++ show w ++ " "++ show c ++ " " ++ show f ++ "\n === " ++ show res++ "\n") res

thm32 :: [LvlVariable] -> [LvlVariable] -> [Horn] -> Model -> Model
thm32 v u c f =
    trace ("\nTHM32 " ++ show v ++ " " ++ show u ++ " "++ show c++ " " ++ show f++ "\n") $
    let res = let (w,f') = forward c f in
              if w==[] then f else
              if u ++ w == v then Map.map (const NInf) f else
              case simplify_ c f' of
                  Just (c',g) ->
                      trace "SIMPLIFICATION NEEDED" $
                      let v' = keys g'
                          g' = thm32 v' (intersect (u ++ w) v') c' g in
                      union f' g'
                  Nothing ->
                      let g = lemma33 v (u ++ w) c f'
                          (w',g') = forward c g in
                      if w'==[] then g else
                      thm32 v (u ++ w ++ w') c g'
    in trace ("\nTHM32 RESULT "++ show v ++ " " ++ show u ++ " "++ show c++ " " ++ show f++ "\n === " ++ show res++ "\n") res

(|>) :: b -> (b -> c) -> c
(|>) = flip ($)

test_cumul :: ()
test_cumul = 
    let a = VarL 1 []
        b = VarL 2 []
        x = VarL 3 []
        vars = [a,b,x]
        horn :: [Horn] = [
            ([(b,3)],(x,0)),
            ([(a,0)],(b,9)),
            ([(b,0),(x,0)],(x,1))
            ]
        model = empty |> 
            insert a (Nat 0) |>
            insert b (Nat 0) |>
            insert x (Nat 0)
        -- fwd_1 = forward vars horn model
        -- !(vars1,fwd1) = trace ("first forward : \n"++ show  fwd_1) fwd_1
        horn2 =  [
            ([(b,3)],(x,0)),
            ([(b,0),(x,0)],(x,1))
            ] 
        -- !fwd_2 = forward vars1 horn2 fwd1
        -- !(vars2,fwd2) = trace ("second forward : \n"++ show  fwd_2) fwd_2
        final_model = empty |> 
            insert a (Nat 0) |>
            insert b (Nat 9) |>
            insert x (Nat 1)
        --final = thm32 [x] [] [] final_model
        final_forward = forward horn2 final_model
        in 
            trace ("result : \n"++ show  final_forward) ()


test_cumul2 :: ()
test_cumul2 = 
    let a = VarL 1 []
        b = VarL 2 []
        c = VarL 3 []
        d = VarL 4 []
        e = VarL 5 []
        vars = [a,b,c,d,e]
        horn :: [Horn] = [
            ([(a,0),(b,0)],(b,1)),
            ([(b,0)],(c,3)),
            ([(c,1)],(d,0)),
            ([(b,0),(d,2)],(e,0))
            ]
        model = empty |> 
            insert a (Nat 0) |>
            insert b (Nat 0) |>
            insert c (Nat 0) |>
            insert d (Nat 0) |>
            insert e (Nat 0)
        --fwd_1 = forward horn model
        -- !(vars1,fwd1) = trace ("first forward : \n"++ show  fwd_1) fwd_1
        --h0 = empty |> 
        --    insert a (Nat 0) |>
        --    insert b (Nat 1) |>
        --    insert c (Nat 4) |>
        --    insert d (Nat 0) |>
        --    insert e (Nat 0)
        --fwd_2 = forward horn h0
        --  !(vars2,fwd2) = trace ("second forward : \n"++ show  fwd_2) fwd_2
        --horn2 =  [
        --    ([(b,3)],(x,0)),
        --    ([(b,0),(x,0)],(x,1))
        --    ] 
        -- !fwd_2 = forward vars1 horn2 fwd1
        -- !(vars2,fwd2) = trace ("second forward : \n"++ show  fwd_2) fwd_2
        --final_model = empty |> 
        --    insert a (Nat 0) |>
        --    insert b (Nat 9) |>
        --    insert x (Nat 1)
        final = thm32 vars [] horn model
        --final_forward = forward [x] horn2 final_model
        in 
            trace ("result : \n"++ show  final) ()
            
module Agda.TypeChecking.Cumulativity where

import Data.Maybe
import Data.List ((\\), delete, intersect)
import Data.Traversable (Traversable)
import Data.Map (Map, (!), union, keys, foldrWithKey, insert, empty)
import qualified Data.Map as Map (map,fold)
import Control.Monad

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad

import Agda.Utils.Impossible
import Control.Exception (assert)

{-# OPTIONS_GHC -ddump-simpl-stats #-}

data LvlVariable  =
      VarL {-# UNPACK #-} !Int Elims
    | MetaL {-# UNPACK #-} !MetaId Elims
    deriving (Eq, Ord)

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
    deriving Eq

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

forward :: [Horn] -> Model -> Model
forward = sorry

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
    let cw = filter (\(x,(y,l)) -> elem y w && all ((flip elem w) . fst) x) c
        g = thm32 w [] cw f
        f_or_g = union f g
        c_down_w = filter (\(x,(y,l)) -> elem y w) c
        g' = forward c_down_w f_or_g
        w' = keys g' in
    if w' == [] then
        f_or_g
    else
        lemma33 v w c (union f g')

thm32 :: [LvlVariable] -> [LvlVariable] -> [Horn] -> Model -> Model
thm32 v u c f =
    let f' = forward c f
        w = keys f' in
    if w==[] then f else
    if u ++ w == v then Map.map (const NInf) f else
    case simplify_ c f' of
        Just (c',g) ->
            let v' = keys g'
                g' = thm32 v' (intersect (u ++ w) v') c' g in
            union f' g'
        Nothing ->
            let g = lemma33 v (u ++ w) c f'
                g' = forward c g
                w' = keys g' in
            if w'==[] then g else
            thm32 v (u ++ w ++ w') c g'
module Agda.TypeChecking.Cumulativity where

import Data.Maybe
import Data.List ((\\), delete)
import Data.Traversable (Traversable)
import Control.Monad

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Free.Lazy
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce

import Agda.Utils.List1 ( List1, pattern (:|) )
import Agda.Utils.Maybe ( caseMaybeM, allJustM )
import Agda.Utils.Monad ( tryMaybe )
import Agda.Utils.Singleton

import Agda.Utils.Impossible
import Control.Exception (assert)
import Agda.Utils.List (isSublistOf)

{-# OPTIONS_GHC -ddump-simpl-stats #-}

data LvlVariable  = 
      VarL {-# UNPACK #-} !Int Elims
    | MetaL {-# UNPACK #-} !MetaId Elims
    deriving Eq

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

type Model = LvlVariable -> NInf

is_satisfied_by :: Horn -> Model -> Bool
is_satisfied_by (x,(y,l)) f =
    if all (\(xi,ki) -> (Nat ki) <= f xi) x 
    then (Nat l) <= f y
    else True

to_nat :: NInf -> Integer
to_nat (Nat n) = n
to_nat _ = __IMPOSSIBLE__

lemma_3_1 :: (LvlVariable -> NInf) -> Horn -> Bool
lemma_3_1 f (x,(y,l)) =
    let w = filter ((/= NInf) . f. fst) x
    in case w of
        [] -> f y == NInf
        _  ->
            let k0 = minimum $ map (\(xi,ki) -> 
                    case f xi of 
                        NInf -> 0 
                        Nat n -> n - ki) 
                    x
            in k0 < 0 || Nat (l+k0) <= f y

--lemma_3_3 v sc trans w f, given W is a strict subset of V,
-- and that for all f models, trans f is the least g>=f model of SC|W, and f a model such that f(v-w) \subset N, computes the least model of SCvW
lemma_3_3 :: [LvlVariable] -> [Horn] -> (Model -> Model) -> [LvlVariable]  -> Model -> Maybe Model
lemma_3_3 v sc trans w f = do
    -- W \subset V strict, f : V -> NInf and f(v-w) \subset N
    guard $ isSublistOf w v && v /= w && all ((NInf /=) . f) (v \\ w)
    let fw      = (w,f)
        maxgain = max_gain sc
        -- gf = least g>=f that models SC|w 
        gf      = trans $ snd fw
        -- Maxgain + max(f(V − W))
        maxf_v_w = maxgain + foldl (flip $ max . to_nat . f) 0 (v \\ w)
        -- Sum for w \in W of max(0,maxf_v_w-gf(w))
        mgf = foldl (\acc w -> acc + (max 0 $ (maxf_v_w - (to_nat $ gf w)))) 0 w
        base_case = Just $ \x -> if elem x w then gf x else f x
    if (mgf == 0)
    then base_case
    else 
        -- List of clauses in SCvW - SC|W not satisfied by gf    
        let leftovers = filter (\(x,(y,l)) -> elem y w && any (not . (flip elem w) . fst) x) sc
            unsat_leftovers = filter (lemma_3_1 gf) leftovers
        in case unsat_leftovers of
            [] ->  base_case
            _  -> 
                let w0 = __IMPOSSIBLE__
                in let f' = \x -> if x == w0 then __IMPOSSIBLE__
                        else if elem x w 
                        then gf x 
                        else f x
                in lemma_3_3 v sc trans (delete w0 w) f'
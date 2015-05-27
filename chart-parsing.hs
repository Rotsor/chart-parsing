{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
import qualified Data.LVar.PureSet as LSet
import qualified Data.Set as Set
import Control.Applicative
import qualified Control.LVish as LVish
import qualified Control.LVish.DeepFrz as Frz
import Data.Traversable
import Data.Foldable hiding(mapM_)
import qualified Data.Vector as V

data Sym =
  A
  | B
  | Dot
  | AList [()]
  | BSeparatedALists [[()]]
  | Sentence [[()]]
    deriving (Eq, Ord, Show)

-- AList = A | A AList
-- BSeparatedALists = AList | BSeparatedALists B BSeparatedALists
-- Sentence = BSeparatedALists Dot

data RuleSyntax =
  FailS
  | ProduceS Sym
  | AList_base
  | AList_recursive0
  | AList_recursive1
  | BList_base
  | BList_recursive0
  | BList_recursive1 [[()]]
  | BList_recursive2 [[()]]
  | Sentence0
  | Sentence1 [[()]]
    deriving (Eq, Ord)

allRules = [AList_base, AList_recursive0, BList_base, BList_recursive0, Sentence0]

simpleRule a b = Require (\s -> if s == a then ProduceS b else FailS)

interpretRuleSyntax :: RuleSyntax -> Rule Sym RuleSyntax
interpretRuleSyntax FailS = Fail
interpretRuleSyntax (ProduceS sym) = Produce sym
interpretRuleSyntax AList_base = simpleRule A (AList [()])
interpretRuleSyntax AList_recursive0 = Require (\case { A -> AList_recursive1; _ -> FailS })
interpretRuleSyntax AList_recursive1 = Require (\case { AList l -> ProduceS (AList (() : l)); _ -> FailS })
interpretRuleSyntax BList_base = Require (\case { AList l -> ProduceS (BSeparatedALists [l]); _ -> FailS})
interpretRuleSyntax BList_recursive0 = Require (\case { BSeparatedALists l -> BList_recursive1 l; _ -> FailS})
interpretRuleSyntax (BList_recursive1 l) = Require (\case { B -> BList_recursive2 l; _ -> FailS})
interpretRuleSyntax (BList_recursive2 l1) = Require (\case { BSeparatedALists l2 -> ProduceS (BSeparatedALists $ l1 ++ l2); _ -> FailS})
interpretRuleSyntax Sentence0 = Require (\case { BSeparatedALists l -> Sentence1 l; _ -> FailS})
interpretRuleSyntax (Sentence1 s) = Require (\case { Dot -> ProduceS (Sentence s) ; _ -> FailS })

data Rule sym rule =
  Fail
  | Produce sym
  | Require (sym -> rule)

instance Frz.DeepFrz Sym where
  type FrzType Sym = Sym

parse :: (Ord sym, Ord rule, Frz.DeepFrz sym, Frz.FrzType sym ~ sym)
         => (rule -> Rule sym rule) -> (sym -> Bool) -> [rule] -> [sym] -> [(sym, Int)]
parse interpretRuleSyntax is_good generic_rules s = filter (is_good . fst) $ Set.toList $ LSet.fromISet $ Frz.runParThenFreeze $ do
  let n = length s
  let positions = V.generate (n + 1) id
  shares <- traverse (\i -> (,) <$> LSet.newEmptySet <*> LSet.newEmptySet) positions
  let messages i = snd $ shares V.! i
  let rules i = fst $ shares V.! i
  forM_ generic_rules $ \rule ->
    forM_ [0..n-1] $ \i ->
      LSet.insert (i, rule) (rules i)
  forM_ (zip [0..] s) $ \(i, word) ->
    LSet.insert (word, 1) (snd $ shares V.! i)
  forM_ [0..n] $ \i ->
    LSet.forEach (rules i) $ \(rule_start, rule) ->
      case interpretRuleSyntax rule of
       Fail -> return ()
       Produce message ->
         LSet.insert (message, i - rule_start) (messages i)
       Require f ->
         if i == n
         then return () -- nothing can start after the end of the string
         else 
         LSet.forEach (messages i) $ \(m, m_length) -> do
           let next_rule = f m
           LSet.insert (rule_start, next_rule) (rules (i + m_length))
  return $ snd $ shares V.! 0

test () = parse interpretRuleSyntax (const True) allRules [A, B, A, A, B, A, Dot]

{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
import qualified Data.LVar.PureSet as ISet
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

interpretRule :: RuleSyntax -> Rule Sym RuleSyntax
interpretRule FailS = Fail
interpretRule (ProduceS sym) = Produce sym
interpretRule AList_base = simpleRule A (AList [()])
interpretRule AList_recursive0 = Require (\case { A -> AList_recursive1; _ -> FailS })
interpretRule AList_recursive1 = Require (\case { AList l -> ProduceS (AList (() : l)); _ -> FailS })
interpretRule BList_base = Require (\case { AList l -> ProduceS (BSeparatedALists [l]); _ -> FailS})
interpretRule BList_recursive0 = Require (\case { BSeparatedALists l -> BList_recursive1 l; _ -> FailS})
interpretRule (BList_recursive1 l) = Require (\case { B -> BList_recursive2 l; _ -> FailS})
interpretRule (BList_recursive2 l1) = Require (\case { BSeparatedALists l2 -> ProduceS (BSeparatedALists $ l1 ++ l2); _ -> FailS})
interpretRule Sentence0 = Require (\case { BSeparatedALists l -> Sentence1 l; _ -> FailS})
interpretRule (Sentence1 s) = Require (\case { Dot -> ProduceS (Sentence s) ; _ -> FailS })

data Rule sym rule =
  Fail
  | Produce sym
  | Require (sym -> rule)

instance Frz.DeepFrz Sym where
  type FrzType Sym = Sym

(!) = (V.!)

parse :: (Ord sym, Ord rule, Frz.DeepFrz sym, Frz.FrzType sym ~ sym)
         => (rule -> Rule sym rule) -> (sym -> Bool) -> [rule] -> [sym] -> [(sym, Int)]
parse interpretRule is_good initial_rules s = filter (is_good . fst) $ Set.toList $ ISet.fromISet $ Frz.runParThenFreeze $ do
  let n = length s
  messages <- V.replicateM (n + 1) ISet.newEmptySet
  rules <- V.replicateM (n + 1) ISet.newEmptySet
  forM_ initial_rules $ \rule ->
    forM_ [0..n-1] $ \i ->
      ISet.insert (i, rule) (rules ! i)
  forM_ (zip [0..] s) $ \(i, word) ->
    ISet.insert (word, 1) (messages ! i)
  forM_ [0..n] $ \i ->
    ISet.forEach (rules ! i) $ \(rule_start, rule) ->
      case interpretRule rule of
       Fail -> return ()
       Produce message ->
         ISet.insert (message, i - rule_start) (messages ! rule_start)
       Require f ->
         ISet.forEach (messages ! i) $ \(m, m_length) -> do
           ISet.insert (rule_start, f m) (rules ! (i + m_length))
  return $ messages ! 0

test () = parse interpretRule (const True) allRules [A, B, A, A, B, A, Dot]
main = mapM_ print $ test ()

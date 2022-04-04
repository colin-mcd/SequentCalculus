module Parse where
import Types
import Helpers

ruleNames = [
  ("Leaf", RuleLeaf),
  ("Cut", RuleCut),
  ("ExchangeL", RuleExchangeL),
  ("ExchangeR", RuleExchangeR),
  ("ContractionL", RuleContractionL),
  ("ContractionR", RuleContractionR),
  ("WeakeningL", RuleWeakeningL),
  ("WeakeningR", RuleWeakeningR),
  ("NegL", RuleNegL),
  ("NegR", RuleNegR),
  ("ConjL", RuleConjL),
  ("ConjR", RuleConjR),
  ("DisjL", RuleDisjL),
  ("DisjR", RuleDisjR),
  ("ImpL", RuleImpL),
  ("ImpR", RuleImpR)
  ]


data Tree = Node String [Tree]

splits :: String -> Maybe [String]
splits x = h 0 "" x where

  add :: String -> Maybe [String] -> Maybe [String]
  add "" mss = mss
  add acc mss = fmap ((:) (reverse acc)) mss
  
  h 0 acc "" = add acc $ Just []
  h p _   "" = Nothing
  h 0 acc (' ' : xs) = add acc $ h 0 "" xs
  h 0 acc (',' : xs) = add acc $ h 0 "" xs
  h 0 acc ('\n' : xs) = add acc $ h 0 "" xs
  h 0 acc ('\t' : xs) = add acc $ h 0 "" xs
  h 0 acc ('(' : xs) = add acc $ h 1 "" xs
  h p acc ('(' : xs) = h (succ p) ('(' : acc) xs
  h 0 acc (')' : xs) = Nothing
  h 1 acc (')' : xs) = add acc $ h 0 "" xs
  h p acc (')' : xs) = h (pred p) (')' : acc) xs
  h p acc (x   : xs) = h p (x : acc) xs

groups :: String -> Maybe Tree
groups xs =
  splits xs >>= \ ss -> case ss of
    [] -> Nothing
    (rl : as) -> pure (Node rl) <*> mapM groups as

tree2proof :: Tree -> Maybe Proof
tree2proof = rule where

  sentence :: Tree -> Maybe Sentence
  sentence (Node "Neg" [x]) = pure Neg <*> sentence x
  sentence (Node "Disj" [x, y]) = pure Disj <*> sentence x <*> sentence y
  sentence (Node "Conj" [x, y]) = pure Conj <*> sentence x <*> sentence y
  sentence (Node "Imp" [x, y]) = pure Imp <*> sentence x <*> sentence y
  sentence (Node a []) = pure (Atom a)
  sentence (Node _ _) = Nothing

  cedent :: Tree -> Maybe Cedent
  cedent (Node l as) = mapM sentence (Node l [] : as)
  
  rule :: Tree -> Maybe Proof
--  rule (Node "Leaf" [Node a []]) = pure (Leaf a)
  rule (Node "Leaf" [s]) = pure leaf <*> sentence s
  rule (Node "Cut" [x, y]) = pure cut <*> rule x <*> rule y
  rule (Node "ExchangeL" [gamma, delta, a, b, x]) = pure exchangeL <*> cedent gamma <*> cedent delta <*> sentence a <*> sentence b <*> rule x
  rule (Node "ExchangeR" [delta, pi, a, b, x]) = pure exchangeR <*> cedent delta <*> cedent pi <*> sentence a <*> sentence b <*> rule x
  rule (Node "WeakeningL" [a, x]) = pure weakeningL <*> sentence a <*> rule x
  rule (Node "WeakeningR" [a, x]) = pure weakeningR <*> sentence a <*> rule x
  rule (Node "ContractionL" [x]) = pure contractionL <*> rule x
  rule (Node "ContractionR" [x]) = pure contractionR <*> rule x
  rule (Node "NegL" [x]) = pure negL <*> rule x
  rule (Node "NegR" [x]) = pure negR <*> rule x
  rule (Node "DisjL" [x, y]) = pure disjL <*> rule x <*> rule y
  rule (Node "DisjR" [x]) = pure disjR <*> rule x
  rule (Node "ConjL" [x]) = pure conjL <*> rule x
  rule (Node "ConjR" [x, y]) = pure conjR <*> rule x <*> rule y
  rule (Node "ImpL" [x, y]) = pure impL <*> rule x <*> rule y
  rule (Node "ImpR" [x]) = pure impR <*> rule x
  rule (Node rl xs) = Nothing

parse :: String -> Maybe Proof
parse x = groups x >>= tree2proof

module Helpers where
import Types

simplify :: Proof -> ProofS
simplify (Leaf a) = (ProofS RuleLeaf [] [Atom a] [])
simplify (Cut g d a x1 x2) = (ProofS RuleCut [g, d] [a] [simplify x1, simplify x2])
simplify (ExchangeL g d p a b x) = (ProofS RuleExchangeL [g, d, p] [a, b] [simplify x])
simplify (ExchangeR g d p a b x) = (ProofS RuleExchangeR [g, d, p] [a, b] [simplify x])
simplify (ContractionL g d a x) = (ProofS RuleContractionL [g, d] [a] [simplify x])
simplify (ContractionR g d a x) = (ProofS RuleContractionR [g, d] [a] [simplify x])
simplify (WeakeningL g d a x) = (ProofS RuleWeakeningL [g, d] [a] [simplify x])
simplify (WeakeningR g d a x) = (ProofS RuleWeakeningR [g, d] [a] [simplify x])
simplify (NegL g d a x) = (ProofS RuleNegL [g, d] [a] [simplify x])
simplify (NegR g d a x) = (ProofS RuleNegR [g, d] [a] [simplify x])
simplify (ConjL g d a b x) = (ProofS RuleConjL [g, d] [a, b] [simplify x])
simplify (ConjR g d a b x1 x2) = (ProofS RuleConjR [g, d] [a, b] [simplify x1, simplify x2])
simplify (DisjL g d a b x1 x2) = (ProofS RuleDisjL [g, d] [a, b] [simplify x1, simplify x2])
simplify (DisjR g d a b x) = (ProofS RuleDisjR [g, d] [a, b] [simplify x])
simplify (ImpL g d a b x1 x2) = (ProofS RuleImpL [g, d] [a, b] [simplify x1, simplify x2])
simplify (ImpR g d a b x) = (ProofS RuleImpR [g, d] [a, b] [simplify x])

expand :: ProofS -> Proof
expand (ProofS RuleLeaf [] [Atom a] []) = (Leaf a)
expand (ProofS RuleCut [g, d] [a] [x1, x2]) = (Cut g d a (expand x1) (expand x2))
expand (ProofS RuleExchangeL [g, d, p] [a, b] [x]) = (ExchangeL g d p a b (expand x))
expand (ProofS RuleExchangeR [g, d, p] [a, b] [x]) = (ExchangeR g d p a b (expand x))
expand (ProofS RuleContractionL [g, d] [a] [x]) = (ContractionL g d a (expand x))
expand (ProofS RuleContractionR [g, d] [a] [x]) = (ContractionR g d a (expand x))
expand (ProofS RuleWeakeningL [g, d] [a] [x]) = (WeakeningL g d a (expand x))
expand (ProofS RuleWeakeningR [g, d] [a] [x]) = (WeakeningR g d a (expand x))
expand (ProofS RuleNegL [g, d] [a] [x]) = (NegL g d a (expand x))
expand (ProofS RuleNegR [g, d] [a] [x]) = (NegR g d a (expand x))
expand (ProofS RuleConjL [g, d] [a, b] [x]) = (ConjL g d a b (expand x))
expand (ProofS RuleConjR [g, d] [a, b] [x1, x2]) = (ConjR g d a b (expand x1) (expand x2))
expand (ProofS RuleDisjL [g, d] [a, b] [x1, x2]) = (DisjL g d a b (expand x1) (expand x2))
expand (ProofS RuleDisjR [g, d] [a, b] [x]) = (DisjR g d a b (expand x))
expand (ProofS RuleImpL [g, d] [a, b] [x1, x2]) = (ImpL g d a b (expand x1) (expand x2))
expand (ProofS RuleImpR [g, d] [a, b] [x]) = (ImpR g d a b (expand x))


weakRules :: [RuleLabel]
weakRules = [RuleExchangeL, RuleExchangeR,
             RuleContractionL, RuleContractionR,
             RuleWeakeningL, RuleWeakeningR]

propRules :: [RuleLabel]
propRules = [RuleNegL, RuleNegR,
             RuleConjL, RuleConjR,
             RuleDisjL, RuleDisjR,
             RuleImpL, RuleImpR]


isCutFreeS :: ProofS -> Bool
isCutFreeS = foldProofS $ \ rl cs ss rs -> rl == RuleCut || or rs
isCutFree = isCutFreeS . simplify

-- Sentence depth
dp :: Sentence -> Int
dp (Atom v) = 0
dp (Neg a) = 1 + dp a
dp (Conj a b) = 1 + max (dp a) (dp b)
dp (Disj a b) = 1 + max (dp a) (dp b)
dp (Imp a b) = 1 + max (dp a) (dp b)

--proofDepthS :: ProofS -> Int
--proofDepthS = foldProofS $ \ rl cs ss rs -> (if rl `elem` weakRules then 0 else 1) + maxOf rs
--proofDepth = proofDepthS . simplify

maxOf :: (Ord n, Num n) => [n] -> n
maxOf = foldr max 0

maxCutDepthS :: ProofS -> Int
maxCutDepthS =
  foldProofSS $ \ rl cs ss ps rs ->
  -- if rl == RuleCut then ss = [s] for some s
  if rl == RuleCut then dp (head ss) else maxOf rs
maxCutDepth :: Proof -> Int
maxCutDepth = maxCutDepthS . simplify

foldN :: (Int -> x -> x) -> x -> Int -> x
foldN s z 0 = z
foldN s z n = s n (foldN s z n)

typeof :: Proof -> (Cedent, Cedent)
typeof (Leaf a) = ([Atom a], [Atom a])
typeof (Cut gamma delta a x1 x2) = ((gamma), (delta))
typeof (ExchangeL gamma delta pi a b x) = ((gamma ++ [b, a] ++ delta), (pi))
typeof (ExchangeR gamma delta pi a b x) = ((gamma), (delta ++ [b, a] ++ pi))
typeof (ContractionL gamma delta a x) = (([a] ++ gamma), (delta))
typeof (ContractionR gamma delta a x) = ((gamma), (delta ++ [a]))
typeof (WeakeningL gamma delta a x) = (([a] ++ gamma), (delta))
typeof (WeakeningR gamma delta a x) = ((gamma), (delta ++ [a]))
typeof (NegL gamma delta a x) = (([Neg a] ++ gamma), (delta))
typeof (NegR gamma delta a x) = ((gamma), (delta ++ [Neg a]))
typeof (ConjL gamma delta a b x) = (([Conj a b] ++ gamma), (delta))
typeof (ConjR gamma delta a b x1 x2) = ((gamma), (delta ++ [Conj a b]))
typeof (DisjL gamma delta a b x1 x2) = (([Imp a b] ++ gamma), (delta))
typeof (DisjR gamma delta a b x) = ((gamma), (delta ++ [Disj a b]))
typeof (ImpL gamma delta a b x1 x2) = (([Imp a b] ++ gamma), (delta))
typeof (ImpR gamma delta a b x) = ((gamma), (delta ++ [Imp a b]))

-- a -> (gamma ==> delta, a) -> (a, gamma ==> delta) -> (gamma ==> delta)
cut :: Proof -> Proof -> Proof
cut x y =
  let (gamma, _) = typeof x
      (a : gamma', delta) = typeof y in
    Cut gamma delta a x y

-- gamma -> delta -> a -> b -> (gamma, a, b, delta ==> pi) -> (gamma, b, a, delta ==> pi)
exchangeL :: Cedent -> Cedent -> Sentence -> Sentence -> Proof -> Proof
exchangeL gamma delta a b x =
  let (_, pi) = typeof x in
    ExchangeL gamma delta pi a b x

-- delta -> pi -> a -> b -> (gamma ==> delta, a, b, pi) -> (gamma ==> delta, b, a, pi)
exchangeR :: Cedent -> Cedent -> Sentence -> Sentence -> Proof -> Proof
exchangeR delta pi a b x =
  let (gamma, _) = typeof x in
    ExchangeR gamma delta pi a b x

-- (a, a, gamma ==> delta) -> (a, gamma ==> delta)
contractionL :: Proof -> Proof
contractionL x =
  let (a : a' : gamma, delta) = typeof x in
    ContractionL gamma delta a x

-- (gamma ==> delta, a, a) -> (gamma ==> delta, a)
contractionR :: Proof -> Proof
contractionR x =
  let (gamma, delta') = typeof x
      (delta, [a, a']) = splitAt (length delta' - 2) delta'
  in
    ContractionR gamma delta a x

-- gamma -> delta -> a -> (gamma, a, a, delta ==> pi) -> (gamma, a, delta ==> pi)
contractionL' :: Cedent -> Cedent -> Sentence -> Proof -> Proof
contractionL' gamma delta a x =
  let (_, pi) = typeof x
      x1 = exchangesAnteL [] gamma (a : delta) a x -- a, gamma, a, delta ==> pi
      x2 = exchangesAnteL [a] gamma delta a x -- a, a, gamma, delta ==> pi
      x3 = contractionL x2 -- a, gamma, delta ==> pi
      x4 = exchangesAnteR [] gamma delta a x3 -- gamma, a, delta ==> pi
  in
    x4

-- delta -> pi -> a -> (gamma ==> delta, a, a, pi) -> (gamma ==> delta, a, pi)
contractionR' :: Cedent -> Cedent -> Sentence -> Proof -> Proof
contractionR' delta pi a x =
  let (gamma, _) = typeof x
      x1 = exchangesSuccR (delta ++ [a]) pi [] a x -- gamma ==> delta, a, pi, a
      x2 = exchangesSuccR delta pi [a] a x1 -- gamma ==> delta, pi, a, a
      x3 = contractionR x2 -- gamma ==> delta, pi, a
      x4 = exchangesSuccL delta pi [] a x3 -- gamma ==> delta, a, pi
  in
    x4


-- a -> (gamma ==> delta) -> (a, gamma ==> delta)
weakeningL :: Sentence -> Proof -> Proof
weakeningL a x =
  let (gamma, delta) = typeof x in
    WeakeningL gamma delta a x

-- a -> (gamma ==> delta) -> (gamma ==> delta, a)
weakeningR :: Sentence -> Proof -> Proof
weakeningR a x =
  let (gamma, delta) = typeof x in
    WeakeningR gamma delta a x

-- gamma -> delta -> a -> (gamma, delta ==> pi) -> (gamma, a, delta ==>> pi)
weakeningL' :: Cedent -> Cedent -> Sentence -> Proof -> Proof
weakeningL' gamma delta a x =
  let (_, pi) = typeof x
      x1 = weakeningL a x -- a, gamma, delta ==> pi
      x2 = exchangesAnteR [] gamma delta a x1 -- gamma, a, delta ==> pi
  in
    x2

-- delta -> pi -> a -> (gamma ==> delta, pi) -> (gamma ==> delta, a, pi)
weakeningR' :: Cedent -> Cedent -> Sentence -> Proof -> Proof
weakeningR' delta pi a x =
  let (gamma, _) = typeof x
      x1 = weakeningR a x -- gamma ==> delta, pi, a
      x2 = exchangesSuccL delta pi [] a x1 -- gamma ==> delta, a, pi
  in
    x2

-- (gamma ==> delta, a) -> (Neg a, gamma ==> delta)
negL :: Proof -> Proof
negL x =
  let (gamma, delta') = typeof x
      (delta, [a]) = splitAt (length delta' - 1) delta' in
    NegL gamma delta a x

-- (a, gamma ==> delta) -> (gamma ==> delta, Neg a)
negR :: Proof -> Proof
negR x =
  let (a : gamma, delta) = typeof x in
    NegR gamma delta a x

-- gamma -> delta -> pi -> lambda -> a -> (gamma, delta ==> pi, a, lambda) -> (gamma, Neg a, delta ==> pi, lambda)
negL' :: Cedent -> Cedent -> Cedent -> Cedent -> Sentence -> Proof -> Proof
negL' gamma delta pi lambda a x =
  let x1 = exchangesSuccR pi lambda [] a x -- gamma, delta ==> pi, lambda, a
      x2 = negL x1 -- Neg a, gamma, delta ==> pi, lambda
      x3 = exchangesAnteR [] gamma delta (Neg a) x2 -- gamma, Neg a, delta ==> pi, lambda
  in
    x3

-- gamma -> delta -> pi -> lambda -> a -> (gamma, a, delta ==> pi, lambda) -> (gamma, delta ==> pi, Neg a, lambda)
negR' :: Cedent -> Cedent -> Cedent -> Cedent -> Sentence -> Proof -> Proof
negR' gamma delta pi lambda a x =
  let x1 = exchangesAnteL [] gamma delta a x -- a, gamma, delta ==> pi, lambda
      x2 = negR x1 -- gamma, delta ==> pi, lambda, Neg a
      x3 = exchangesSuccL pi lambda [] (Neg a) x2 -- gamma, delta ==> pi, Neg a, lambda
  in
    x3

-- (a, b, gamma ==> delta) -> (Conj a b, gamma ==> delta)
conjL :: Proof -> Proof
conjL x =
  let (a : b : gamma, delta) = typeof x in
    ConjL gamma delta a b x

-- (gamma ==> delta, a) -> (gamma ==> delta, b) -> (gamma ==> delta, Conj a b)
conjR :: Proof -> Proof -> Proof
conjR x y =
  let (gammax, delta_a) = typeof x
      (gammay, delta_b) = typeof y
      (deltax, [a]) = splitAt (length delta_a - 1) delta_a
      (deltay, [b]) = splitAt (length delta_b - 1) delta_b
  in
    ConjR gammax deltax a b x y

-- gamma -> delta -> a -> b -> (gamma, a, b, delta ==> pi) -> (gamma, Conj a b, delta ==> pi)
conjL' :: Cedent -> Cedent -> Sentence -> Sentence -> Proof -> Proof
conjL' gamma delta a b x =
  let x1 = exchangesAnteL [] gamma (b : delta) a x -- a, gamma, b, delta ==> pi
      x2 = exchangesAnteL [a] gamma delta b x1 -- a, b, gamma, delta ==> pi
      x3 = conjL x2 -- Conj a b, gamma, delta ==> pi
      x4 = exchangesAnteR [] gamma delta (Conj a b) x3 -- gamma, Conj a b, delta ==> pi
  in
    x4

-- delta -> pi -> a -> b -> (gamma ==> delta, a, pi) -> (gamma ==> delta, b, pi) -> (gamma ==> delta, Conj a b, pi)
conjR' :: Cedent -> Cedent -> Sentence -> Sentence -> Proof -> Proof -> Proof
conjR' delta pi a b x y =
  let x1 = exchangesSuccR delta pi [] a x -- gamma ==> delta, pi, a
      y1 = exchangesSuccR delta pi [] b y -- gamma ==> delta, pi, b
      z1 = conjR x1 y1 -- gamma ==> delta, pi, Conj a b
      z2 = exchangesSuccL delta pi [] (Conj a b) z1
  in
    z2

--(a, gamma ==> delta) -> (b, gamma ==> delta) -> (Disj a b, gamma ==> delta)
disjL :: Proof -> Proof -> Proof
disjL x y =
  let (a : gammax, deltax) = typeof x
      (b : gammay, deltay) = typeof y
  in
    DisjL gammax deltax a b x y

-- (gamma ==> delta, a, b) -> (gamma ==> delta, Disj a b)
disjR :: Proof -> Proof
disjR x =
  let (gamma, delta_a_b) = typeof x
      (delta, [a, b]) = splitAt (length delta_a_b - 2) delta_a_b in
    DisjR gamma delta a b x

-- gamma -> delta -> a -> b -> (gamma, a, delta ==> pi) -> (gamma, b, delta ==> pi) -> (gamma, Disj a b, delta ==> pi)
disjL' :: Cedent -> Cedent -> Sentence -> Sentence -> Proof -> Proof -> Proof
disjL' gamma delta a b x y =
  let x1 = exchangesAnteL [] gamma delta a x -- a, gamma, delta ==> pi
      y1 = exchangesAnteL [] gamma delta a y -- b, gamma, delta ==> pi
      z1 = disjL x1 y1 -- Conj a b, gamma, delta ==> pi
      z2 = exchangesAnteR [] gamma delta (Conj a b) z1 -- gamma, Conj a b, delta ==> pi
  in
    z2

-- delta -> pi -> a -> b -> (gamma ==> delta, a, b, pi) -> (gamma ==> delta, Disj a b, pi)
disjR' :: Cedent -> Cedent -> Sentence -> Sentence -> Proof -> Proof
disjR' delta pi a b x =
  let x1 = exchangesSuccR (delta ++ [a]) pi [] b x -- gamma ==> delta, a, pi, b
      x2 = exchangesSuccR delta pi [b] a x1 -- gamma ==> delta, pi, a, b
      x3 = disjR x2 -- gamma ==> delta, pi, Disja b
      x4 = exchangesSuccL delta pi [] (Disj a b) x3 -- gamma ==> delta, Disj a b, pi
  in
    x4

-- (gamma ==> delta, a) -> (b, gamma ==> delta) -> (Imp a b, gamma ==> delta)
impL :: Proof -> Proof -> Proof
impL x y =
  let (gammax, deltax_a) = typeof x
      (b : gammay, deltay) = typeof y
      (deltax, [a]) = splitAt (length deltax_a - 1) deltax_a in
    ImpL gammax deltax a b x y

-- (a, gamma ==> delta, b) -> (gamma ==> delta, Imp a b)
impR :: Proof -> Proof
impR x =
  let (a : gamma, delta_b) = typeof x
      (delta, [b]) = splitAt (length delta_b - 1) delta_b in
    ImpR gamma delta a b x

-- gamma -> delta -> pi -> lambda -> a -> b -> (gamma, delta ==> pi, a, lambda) -> (gamma, b, delta ==> pi, lambda) -> (gamma, Imp a b, delta ==> pi, lambda)
impL' :: Cedent -> Cedent -> Cedent -> Cedent -> Sentence -> Sentence -> Proof -> Proof -> Proof
impL' gamma delta pi lambda a b x y =
  let x1 = exchangesSuccR pi lambda [] a x -- gamma, delta ==> pi, lambda, a
      y1 = exchangesSuccL [] gamma delta b y -- b, gamma, delta ==> pi, lambda
      z1 = impL x1 y1 -- Imp a b, gamma, delta ==> pi, lambda
      z2 = exchangesAnteR [] gamma delta (Imp a b) z1 -- gamma, Imp a b, delta ==> pi, lambda
  in
    z2

-- gamma -> delta -> pi -> lambda -> a -> b -> (gamma, a, delta ==> pi, b, lambda) -> (gamma, delta ==> pi, Imp a b, lambda)
impR' :: Cedent -> Cedent -> Cedent -> Cedent -> Sentence -> Sentence -> Proof -> Proof
impR' gamma delta pi lambda a b x =
  let x1 = exchangesAnteL [] gamma delta a x -- a, gamma, delta ==> pi, b, lambda
      x2 = exchangesSuccR pi lambda [] b x1 -- a, gamma, delta ==> pi, lambda, b
      x3 = impR x2 -- gamma, delta ==> pi, lambda, Imp a b
      x4 = exchangesSuccL pi lambda [] (Imp a b) x3 -- gamma, delta ==> pi, Imp a b, lambda
  in
    x4

-- gamma -> delta -> pi -> a ->
--   (gamma, delta, a, pi ==> lambda) -> (gamma, a, delta, pi ==> lambda)
exchangesAnteL :: Cedent -> Cedent -> Cedent -> Sentence -> Proof -> Proof
exchangesAnteL gamma delta pi a x = h delta where
  (_, lambda) = typeof x
  h [] = x
  h (b : delta) = exchangeL gamma (delta ++ pi) b a (h delta)

-- gamma -> delta -> pi -> a ->
--   (gamma, a, delta, pi ==> lambda) -> (gamma, delta, a, pi ==> lambda)
exchangesAnteR :: Cedent -> Cedent -> Cedent -> Sentence -> Proof -> Proof
exchangesAnteR gamma delta pi a x = h gamma delta x where
  (_, lambda) = typeof x
  h gamma [] x = x
  h gamma (b : delta) x =
    h (gamma ++ [b]) delta (exchangeL gamma (delta ++ pi) a b x)

-- delta -> pi -> lambda -> a ->
--   (gamma ==> delta, pi, a, lambda) -> (gamma ==> delta, a, pi, lambda)
exchangesSuccL :: Cedent -> Cedent -> Cedent -> Sentence -> Proof -> Proof
exchangesSuccL delta pi lambda a x = h pi where
  (gamma, _) = typeof x
  h [] = x
  h (b : pi) =
    -- x :: (gamma => delta, b, pi, a, lambda)
    -- want (gamma => delta, a, b, pi, lambda)
    exchangeR delta (pi ++ lambda) b a (h pi)
  
-- delta -> pi -> lambda -> a ->
--   (gamma ==> delta, a, pi, lambda) -> (gamma ==> delta, pi, a, lambda)
exchangesSuccR :: Cedent -> Cedent -> Cedent -> Sentence -> Proof -> Proof
exchangesSuccR delta pi lambda a x = h delta pi x where
  (gamma, _) = typeof x
  h delta [] x = x
  h delta (b : pi) x =
    -- x :: (gamma ==> delta, a, b, pi, lambda)
    -- want (gamma ==> delta, b, pi, a, lambda)
    h (delta ++ [b]) pi (exchangeR delta (pi ++ lambda) a b x)

-- a -> (delta ==> pi) -> (delta, a ==> pi)
weakeningAnteR :: Sentence -> Proof -> Proof
weakeningAnteR a x =
  let (delta, pi) = typeof x in
    exchangesAnteR [] delta [] a (weakeningL a x)

-- a -> (delta ==> pi) -> (delta ==> a, pi)
weakeningSuccL :: Sentence -> Proof -> Proof
weakeningSuccL a x =
  let (delta, pi) = typeof x
      x1 = x -- delta ==> pi
      x2 = weakeningR a x1 -- delta ==> pi, a
      x3 = exchangesSuccL [] pi [] a x2 -- delta ==> a, pi
  in
    x3

-- gamma -> (delta ==> pi) -> (gamma, delta ==> pi)
weakeningsAnteL :: Cedent -> Proof -> Proof
weakeningsAnteL [] x = x
weakeningsAnteL (g : gamma) x =
  let (delta, pi) = typeof x in
    weakeningL g (weakeningsAnteL gamma x)

-- gamma -> (delta ==> pi) -> (delta, gamma ==> pi)
weakeningsAnteR :: Cedent -> Proof -> Proof
weakeningsAnteR [] x = x
weakeningsAnteR (g : gamma) x =
  let (delta, pi) = typeof x in
    weakeningL g (weakeningsAnteR gamma x)

-- gamma -> (delta ==> pi) -> (delta ==> gamma, pi)
weakeningsSuccL :: Cedent -> Proof -> Proof
weakeningsSuccL [] x = x
weakeningsSuccL (g : gamma) x =
  -- want: delta ==> g, gamma, pi
  let (delta, pi) = typeof x
      x1 = x -- delta ==> pi
      x2 = weakeningsSuccL gamma x -- delta ==> gamma, pi
      x3 = weakeningSuccL g x2 -- delta ==> g, gamma, pi
  in
    x3

-- gamma -> (delta ==> pi) -> (delta ==> pi, gamma)
weakeningsSuccR :: Cedent -> Proof -> Proof
weakeningsSuccR [] x = x
weakeningsSuccR (g : gamma) x =
  let (delta, pi) = typeof x in
    weakeningsSuccR gamma (weakeningR g x)

-- (anteL, anteR, succL, succR) -> (gamma ==> delta)
--   -> (anteL, gamma, anteR ==> succL, delta, succR)
weakenings :: (Cedent, Cedent, Cedent, Cedent) -> Proof -> Proof
weakenings (anteL, anteR, succL, succR) x =
  weakeningsAnteL anteL $
  weakeningsAnteR anteR $
  weakeningsSuccR succR $
  weakeningsSuccL succL x


-- delta -> (gamma ==> delta') -> (gamma ==> delta)  (assumes delta' \subset delta)
weakeningLto :: Cedent -> Proof -> Proof
weakeningLto delta x = h [] delta' delta x where
  (gamma, delta') = typeof x
  -- pi -> delta' -> delta -> (gamma ==> pi, delta') -> (gamma ==> pi, delta)
  h :: Cedent -> Cedent -> Cedent -> Proof -> Proof
  h pi (d' : delta') [] x =
    error "this shouldn't happen"
  h pi [] delta x =
    -- x: gamma ==> pi
    -- want: gamma ==> pi, delta
    weakenings ([], [], [], delta) x
  h pi (d' : delta') (d : delta) x
    | d' == d = h (pi ++ [d]) delta' delta x
    | otherwise =
      -- want: gamma ==> pi, d, delta
      -- x: gamma ==> pi, d', delta'
      let x1 = weakeningR d x -- gamma ==> pi, d', delta', d
          x2 = exchangesSuccL pi (d' : delta') [] d x1 -- gamma ==> pi, d, d', delta'
          x3 = h (pi ++ [d]) (d' : delta') delta x2 -- gamma ==> pi, d, delta
      in
        x3

-- gamma -> (gamma' ==> delta) -> (gamma ==> delta)  (assumes gamma' \subset gamma)
weakeningRto :: Cedent -> Proof -> Proof
weakeningRto gamma x = h [] gamma' gamma x where
  (gamma', delta) = typeof x
  -- pi -> gamma' -> gamma -> (pi, gamma' ==> delta) -> (pi, gamma ==> delta)
  h :: Cedent -> Cedent -> Cedent -> Proof -> Proof
  h pi (g' : gamma') [] x =
    error "this shouldn't happen"
  h pi [] gamma x =
    -- x: pi ==> delta
    -- want: pi, gamma ==> delta
    weakenings ([], gamma, [], []) x
  h pi (g' : gamma') (g : gamma) x
    | g' == g = h (pi ++ [g]) gamma' gamma x
    | otherwise =
      -- want: pi, g, gamma ==> delta
      -- x: pi, g', gamma' ==> delta
      let x1 = h pi (g' : gamma') gamma x -- pi, gamma ==> delta
          x2 = weakeningL g x1 -- g, pi, gamma ==> delta
          x3 = exchangesAnteR [] pi gamma g x2 -- pi, g, gamma ==> delta
      in
        x3

-- contractDouble :: gamma -> delta -> (gamma, gamma ==> delta, delta) -> (gamma ==> delta)
contractDouble :: Cedent -> Cedent -> Proof -> Proof
contractDouble gamma delta x = contractDoubleL gamma (contractDoubleR delta x)

-- contractDoubleL :: gamma -> (gamma, gamma ==> delta) -> (gamma ==> delta)
contractDoubleL :: Cedent -> Proof -> Proof
contractDoubleL gamma x = h [] gamma x where
  (_, delta) = typeof x
  -- pi -> gamma -> (pi, gamma, gamma ==> delta) -> (pi, gamma ==> delta)
  h pi [] x = x
  h pi (g : gamma) x =
    -- x: pi, g, gamma, g, gamma ==> delta
    -- want: pi, g, gamma ==> delta
    let x1 = exchangesAnteL [] pi (gamma ++ g : gamma) g x -- g, pi, gamma, g, gamma ==> delta
        x2 = exchangesAnteL [g] (pi ++ gamma) gamma g x1 -- g, g, pi, gamma, gamma ==> delta
        x3 = contractionL x2 -- g, pi, gamma, gamma ==> delta
        x4 = exchangesAnteR [] pi (gamma ++ gamma) g x3 -- pi, g, gamma, gamma ==> delta
        x5 = h (pi ++ [g]) gamma x4 -- pi, g, gamma ==> delta
    in
      x5

-- contractDoubleR :: delta -> (gamma ==> delta, delta) -> (gamma ==> delta)
contractDoubleR :: Cedent -> Proof -> Proof
contractDoubleR delta x = h [] delta x where
  (gamma, _) = typeof x
  -- pi -> delta -> (gamma ==> pi, delta, delta) -> (gamma ==> pi, delta)
  h pi [] x = x
  h pi (d : delta) x =
    -- x: gamma ==> pi, d, delta, d, delta
    -- want: gamma ==> pi, d, delta
    let x1 = exchangesSuccR (pi ++ d : delta) delta [] d x1 -- gamma ==> pi, d, delta, delta, d
        x2 = exchangesSuccR pi (delta ++ delta) [d] d x2 -- gamma ==> pi, delta, delta, d, d
        x3 = contractionR x2 -- gamma ==> pi, delta, delta, d
        x4 = exchangesSuccL pi (delta ++ delta) [] d x3 -- gamma ==> pi, d, delta, delta
        x5 = h (pi ++ [d]) delta x4 -- gamma ==> pi, d, delta
    in
      x5

--------------------------------------------------------------------------------

{-
typeof (Leaf a) = error "TODO"
typeof (Cut gamma delta a x1 x2) = error "TODO"
typeof (ExchangeL gamma delta pi a b x) = error "TODO"
typeof (ExchangeR gamma delta pi a b x) = error "TODO"
typeof (ContractionL gamma delta a x) = error "TODO"
typeof (ContractionR gamma delta a x) = error "TODO"
typeof (WeakeningL gamma delta a x) = error "TODO"
typeof (WeakeningR gamma delta a x) = error "TODO"
typeof (NegL gamma delta a x) = error "TODO"
typeof (NegR gamma delta a x) = error "TODO"
typeof (ConjL gamma delta a b x) = error "TODO"
typeof (ConjR gamma delta a b x1 x2) = error "TODO"
typeof (DisjL gamma delta a b x1 x2) = error "TODO"
typeof (DisjR gamma delta a b x) = error "TODO"
typeof (ImpL gamma delta a b x1 x2) = error "TODO"
typeof (ImpR gamma delta a b x) = error "TODO"
-}

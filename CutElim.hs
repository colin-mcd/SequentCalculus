module CutElim where
import Types
import Helpers

deleteDAs :: Sentence -> Cedent -> Cedent
deleteDAs = filter . (/=)

infix 9 -*
(-*) :: Cedent -> Sentence -> Cedent
(-*) = flip deleteDAs

-- f -> c -> (gamma ==> delta) -> (anteL, gamma, anteR ==> succL, (delta -* c), succR)
-- First arg (f) is a special case for when delPatchR'ing with c = (Neg ...) and the
-- rule NegR, or c = (Conj ...) and ConjL, etc. It takes the delPatchR'd proof and the
-- original proof and returns what to do in this special case
-- See pp. 38-39 in Buss' Handbook of Proof Theory, ch. 1
delPatchR :: ([Proof] -> Proof -> Proof) -> Sentence -> (Cedent, Cedent, Cedent, Cedent) -> Proof -> Proof
delPatchR f c ws@(anteL, anteR, succL, succR) (Leaf a) =
  if c == Atom a then
    -- want: anteL, a, anteR ==> succL, succR
    f [] (Leaf a)
  else
    -- want: anteL, a, anteR ==> succL, a, succR
    let x1 = Leaf a -- a ==> a
        x2 = weakenings ws x1 -- anteL, a, anteR ==> succL, a, succR
    in
      x2
delPatchR f c ws@(anteL, anteR, succL, succR) (Cut gamma delta a x y) =
  -- x: gamma ==> delta, a
  -- y: a, gamma ==> delta
  -- want: anteL, gamma, anteR ==> succL, (delta -* c), succR
  if c == a then
    delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), succR
  else
    let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), a, succR
        x2 = exchangesSuccR [] (succL ++ (delta -* c)) succR a x1 -- anteL, gamma, anteR ==> a, succL, (delta -* c), succR
        y1 = delPatchR f c ws y -- anteL, a, gamma, anteR ==> succL, (delta -* c), succR
        y2 = exchangesAnteL [] anteL (gamma ++ anteR) a y1 -- anteL, gamma, anteR, a ==> succL, (delta -* c), succR
    in
      cut x2 y2
delPatchR f c ws@(anteL, anteR, succL, succR) (ExchangeL gamma delta pi a b x) =
  -- x: gamma, a, b, delta ==> pi
  -- want: anteL, gamma, b, a, delta, anteR ==> succL, (pi -* c), succR
  let x1 = delPatchR f c ws x -- anteL, gamma, a, b, delta, anteR ==> succL, (pi -* c), succR
      x2 = exchangeL (anteL ++ gamma) (delta ++ anteR) a b x1 -- anteL, gamma, b, a, delta, anteR ==> succL, (pi -* c), succR
  in
    x2
delPatchR f c ws@(anteL, anteR, succL, succR) (ExchangeR gamma delta pi a b x) =
  -- x: gamma ==> delta, a, b, pi
  -- want: anteL, gamma, anteR ==> succL, ((delta, b, a, pi) -* c), succR
  if c == a || c == b then
    delPatchR f c ws x -- No need to exchange a and b because one/both get deleted
  else
    let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), a, b, (pi -* c), succR
        x2 = exchangeR (succL ++ (delta -* c)) ((pi -* c) ++ succR) a b x1 -- anteL, gamma, anteR ==> succL, (delta -* c), b, a (pi -* c), succR
    in
      x2
delPatchR f c ws@(anteL, anteR, succL, succR) (ContractionL gamma delta a x) =
  -- x: a, a, gamma ==> delta
  -- want: anteL, a, gamma, anteR ==> succL, (delta -* c), succR
  let x1 = delPatchR f c ws x -- anteL, a, a, gamma, anteR ==> succL, (delta -* c), succR
      x2 = exchangesAnteL [] anteL (a : gamma ++ anteR) a x1 -- a, anteL, a, gamma, anteR ==> succL, (delta -* c), succR
      x3 = exchangesAnteL [a] anteL (gamma ++ anteR) a x2 -- a, a, anteL, gamma, anteR ==> succL, (delta -* c), succR
      x4 = contractionL x3 -- a, anteL, gamma, anteR ==> succL, (delta -* c), succR
      x5 = exchangesAnteR [] anteL (gamma ++ anteR) a x4 -- anteL, a, gamma, anteR ==> succL, (delta -* c), succR
  in
    x5
delPatchR f c ws@(anteL, anteR, succL, succR) (ContractionR gamma delta a x) =
  -- x: gamma ==> delta, a, a
  -- want: anteL, gamma, anteR ==> succL, (delta -* c), (a -* c), succR
  if c == a then
    delPatchR f c ws x -- no need to contract because a was deleted
  else
    let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), a, a, succR
        x2 = exchangesSuccR (succL ++ (delta -* c) ++ [a]) succR [] a x1 -- anteL, gamma, anteR ==> succL, (delta -* c), a, succR, a
        x3 = exchangesSuccR (succL ++ (delta -* c)) succR [a] a x2 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a, a
        x4 = contractionR x3 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a
        x5 = exchangesSuccL (succL ++ (delta -* c)) succR [] a x4 -- anteL, gamma, anteR ==> succL, (delta -* c), a, succR
    in
      x5
delPatchR f c ws@(anteL, anteR, succL, succR) (WeakeningL gamma delta a x) =
  -- x: gamma ==> delta
  -- want: anteL, a, gamma, anteR ==> succL, (delta -* c), succR
  let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), succR
      x2 = weakeningL a x1 -- a, anteL, gamma, anteR ==> succL, (delta -* c), succR
      x3 = exchangesAnteR [] anteL (gamma ++ anteR) a x2 -- anteL, a, gamma, anteR ==> succL, (delta -* c), succR
  in
    x3
delPatchR f c ws@(anteL, anteR, succL, succR) (WeakeningR gamma delta a x) =
  -- x: gamma ==> delta
  -- want: anteL, gamma, anteR ==> succL, (delta -* c), (a -* c), succR
  if c == a then
    delPatchR f c ws x -- no need to weaken because a was deleted
  else
    let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), succR
        x2 = weakeningR a x1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a
        x3 = exchangesSuccL (succL ++ (delta -* c)) succR [] a x2 -- anteL, gamma, anteR ==> succL, (delta -* c), a, succR
    in
      x3
delPatchR f c ws@(anteL, anteR, succL, succR) (NegL gamma delta a x) =
  -- x: gamma ==> delta, a
  -- want: anteL, (Neg a), gamma, anteR ==> succL, (delta -* c), succR
  if c == a then
    let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), succR
        x2 = weakeningL (Neg a) x1 -- (Neg a), anteL, gamma, anteR ==> succL, (delta -* c), succR
        x3 = exchangesAnteR [] anteL (gamma ++ anteR) (Neg a) x2 -- anteL, (Neg a), gamma, anteR ==> succL, (delta -* c), succR
    in
      x3
  else
    let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), a, succR
        x2 = exchangesSuccR (succL ++ (delta -* c)) succR [] a x1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a
        x3 = negL x2 -- (Neg a), anteL, gamma, anteR ==> succL, (delta -* c), succR
        x4 = exchangesAnteR [] anteL (gamma ++ anteR) (Neg a) x3 -- anteL, (Neg a), gamma, anteR ==> succL, (delta -* c), succR
    in
      x4
delPatchR f c ws@(anteL, anteR, succL, succR) (NegR gamma delta a x) =
  -- x: a, gamma ==> delta
  -- want: anteL, gamma, anteR ==> succL, (delta -* c), (Neg a -* c), succR
  if c == Neg a then
    let x1 = delPatchR f c ws x -- anteL, a, gamma, anteR ==> succL, (delta -* c), succR
        x2 = f [x1] (NegR gamma delta a x) -- anteL, gamma, anteR ==> succL, (delta -* c), succR
    in
      x2
  else
    let x1 = delPatchR f c ws x -- anteL, a, gamma, anteR ==> succL, (delta -* c), succR
        x2 = exchangesAnteL [] anteL (gamma ++ anteR) a x1 -- a, anteL, gamma, anteR ==> succL, (delta -* c), succR
        x3 = negR x2 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Neg a)
        x4 = exchangesSuccL (succL ++ (delta -* c)) succR [] (Neg a) x3 -- anteL, gamma, anteR ==> succL, (delta -* c), (Neg a), succR
    in
      x4
delPatchR f c ws@(anteL, anteR, succL, succR) (ConjL gamma delta a b x) =
  -- x: a, b, gamma ==> delta
  -- want: anteL, (Conj a b), gamma, anteR ==> succL, (delta -* c), succR
  let x1 = delPatchR f c ws x -- anteL, a, b, gamma, anteR ==> succL, (delta -* c), succR
      x2 = exchangesAnteL [] anteL (b : gamma ++ anteR) a x1 -- a, anteL, b, gamma, anteR ==> succL, (delta -* c), succR
      x3 = exchangesAnteL [a] anteL (gamma ++ anteR) a x2 -- a, b, anteL, gamma, anteR ==> succL, (delta -* c), succR
      x4 = conjL x3 -- (Conj a b), anteL, gamma, anteR ==> succL, (delta -* c), succR
      x5 = exchangesAnteR [] anteL (gamma ++ anteR) (Conj a b) x4 -- anteL, (Conj a b), gamma, anteR ==> succL, (delta -* c), succR
  in
    x5
delPatchR f c ws@(anteL, anteR, succL, succR) (ConjR gamma delta a b x y) =
  -- x: gamma ==> delta, a
  -- y: gamma ==> delta, b
  -- want: anteL, gamma, anteR ==> succL, (delta -* c), (Conj a b -* c), succR
  if c == Conj a b then
    f [delPatchR f c ws x, delPatchR f c ws y] (ConjR gamma delta a b x y)
  else
    let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), (a -* c), succR
        y1 = delPatchR f c ws y -- anteL, gamma, anteR ==> succL, (delta -* c), (b -* c), succR
    in
      if c == a then
        let x2 = weakeningR (Conj a b) x1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Conj a b)
            x3 = exchangesSuccL (succL ++ (delta -* c)) succR [] (Conj a b) x2 -- anteL, gamma, anteR ==> succL, (delta -* c), (Conj a b), succR
        in
          x3
      else if c == b then
        let y2 = weakeningR (Conj a b) y1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Conj a b)
            y3 = exchangesSuccL (succL ++ (delta -* c)) succR [] (Conj a b) y2 -- anteL, gamma, anteR ==> succL, (delta -* c), (Conj a b), succR
        in
          y3
      else
        let x2 = exchangesSuccR (succL ++ (delta -* c)) succR [] a x1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a
            y2 = exchangesSuccR (succL ++ (delta -* c)) succR [] b y1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, b
            z1 = conjR x2 y2 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Conj a b)
            z2 = exchangesSuccL (succL ++ (delta -* c)) succR [] (Conj a b) z1 -- anteL, gamma, anteR ==> succL, (delta -* c), (Conj a b), succR
        in
          z2
delPatchR f c ws@(anteL, anteR, succL, succR) (DisjL gamma delta a b x y) =
  -- x: a, gamma ==> delta
  -- y: b, gamma ==> delta
  -- want: anteL, (Disj a b), gamma, anteR ==> succL, (delta -* c), succR
  let x1 = delPatchR f c ws x -- anteL, a, gamma, anteR ==> succL, (delta -* c), succR
      y1 = delPatchR f c ws y -- anteL, b, gamma, anteR ==> succL, (delta -* c), succR
      x2 = exchangesAnteL [] anteL (gamma ++ anteR) a x1 -- a, anteL, gamma, anteR ==> succL, (delta -* c), succR
      y2 = exchangesAnteL [] anteL (gamma ++ anteR) b y1 -- b, anteL, gamma, anteR ==> succL, (delta -* c), succR
      z1 = disjL x2 y2 -- (Disj a b), anteL, gamma, anteR ==> succL, (delta -* c), succR
      z2 = exchangesAnteR [] anteL (gamma ++ anteR) (Disj a b) z1 -- anteL, (Disj a b), gamma, anteR ==> succL, (delta -* c), succR
  in
    z2
delPatchR f c ws@(anteL, anteR, succL, succR) (DisjR gamma delta a b x) =
  -- x: gamma ==> delta, a, b
  -- want: anteL, gamma, anteR ==> succL, (delta -* c), (Disj a b -* c), succR
  let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), (a -* c), (b -* c), succR
  in
    if c == Disj a b then
      f [x1] (DisjR gamma delta a b x)
    else
      if c == a && c == b then
        let x2 = weakeningR (Disj a b) x1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Disj a b)
            x3 = exchangesSuccL (succL ++ (delta -* c)) succR [] (Disj a b) x2 -- anteL, gamma, anteR ==> succL, (delta -* c), (Disj a b), succR
        in
          x3
      else if c == a then
        let x2 = weakeningR a x1 -- anteL, gamma, anteR ==> succL, (delta -* c), b, succR, a
            x3 = exchangesSuccR (succL ++ (delta -* c)) (succR ++ [a]) [] b x2 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a, b
            x4 = disjR x3 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Disj a b)
            x5 = exchangesSuccL (succL ++ (delta -* c)) succR [] (Disj a b) x4 -- anteL, gamma, anteR ==> succL, (delta -* c), (Disj a b), succR
        in
          x5
      else if c == b then
        let x2 = weakeningR b x1 -- anteL, gamma, anteR ==> succL, (delta -* c), a, succR, b
            x3 = exchangesSuccR (succL ++ (delta -* c)) succR [b] a x2 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a, b
            x4 = disjR x3 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Disj a b)
            x5 = exchangesSuccL (succL ++ (delta -* c)) succR [] (Disj a b) x4 -- anteL, gamma, anteR ==> succL, (delta -* c), (Disj a b), succR
        in
          x5
      else
        let x2 = exchangesSuccR (succL ++ (delta -* c) ++ [a]) succR [] b x1 -- anteL, gamma, anteR ==> succL, (delta -* c), a, succR, b
            x3 = exchangesSuccR (succL ++ (delta -* c)) succR [b] a x2 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a, b
            x4 = disjR x3 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Disj a b)
            x5 = exchangesSuccL (succL ++ (delta -* c)) succR [] (Disj a b) x4
        in
          x5
delPatchR f c ws@(anteL, anteR, succL, succR) (ImpL gamma delta a b x y) =
  -- x: gamma ==> delta, a
  -- y: b, gamma ==> delta
  -- want: anteL, (Imp a b), gamma, anteR ==> succL, (delta -* c), succR
  let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), (a -* c), succR
      y1 = delPatchR f c ws y -- anteL, b, gamma, anteR ==> succL, (delta -* c), succR
      x2 = if c == a then weakeningR a x1 else exchangesSuccR (succL ++ (delta -* c)) succR [] a x1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a
      y2 = exchangesAnteL [] anteL (gamma ++ anteR) b y1 -- b, anteL, gamma, anteR ==> succL, (delta -* c), succR
      z1 = impL x2 y2 -- (Imp a b), anteL, gamma, anteR ==> succL, (delta -* c), succR
      z2 = exchangesAnteR [] anteL (gamma ++ anteR) (Imp a b) z1
  in
    z2
delPatchR f c ws@(anteL, anteR, succL, succR) (ImpR gamma delta a b x) =
  -- x: a, gamma ==> delta, b
  -- want: anteL, gamma, anteR ==> succL, (delta -* c), (Imp a b -* c), succR
  if c == Imp a b then
    f [delPatchR f c ws x] (ImpR gamma delta a b x)
  else
    let x1 = delPatchR f c ws x -- anteL, a, gamma, anteR ==> succL, (delta -* c), (b -* c), succR
        x2 = exchangesAnteL [] anteL (gamma ++ anteR) a x1 -- a, anteL, gamma, anteR ==> succL, (delta -* c), (b -* c), succR
        x3 = if c == a then weakeningR b x1 else exchangesSuccR (succL ++ (delta -* c)) succR [] b x2 -- a, anteL, gamma, anteR ==> succL, (delta -* c), succR, b
        x4 = impR x3 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Imp a b)
        x5 = exchangesSuccL (succL ++ (delta -* c)) succR [] (Imp a b) x4 -- anteL, gamma, anteR ==> succL, (delta -* c), (Imp a b), succR
    in
      x5

-- f -> c -> (gamma ==> delta) -> (anteL, (gamma -* c), anteR ==> succL, delta, succR)
delPatchL :: ([Proof] -> Proof -> Proof) -> Sentence -> (Cedent, Cedent, Cedent, Cedent) -> Proof -> Proof
delPatchL f c ws@(anteL, anteR, succL, succR) (Leaf a) =
  -- want: anteL, (a -* c), anteR ==> succL, a, succR
  if c == Atom a then
    f [] (Leaf a)
  else
    let x1 = Leaf a -- a ==> a
        x2 = weakenings ws x1 -- anteL, a, anteR ==> succL, a, succR
    in
      x2
delPatchL f c ws@(anteL, anteR, succL, succR) (Cut gamma delta a x y) =
  error "TODO"
delPatchL f c ws@(anteL, anteR, succL, succR) (ExchangeL gamma delta pi a b x) =
  error "TODO"
delPatchL f c ws@(anteL, anteR, succL, succR) (ExchangeR gamma delta pi a b x) =
  error "TODO"
delPatchL f c ws@(anteL, anteR, succL, succR) (ContractionL gamma delta a x) =
  error "TODO"
delPatchL f c ws@(anteL, anteR, succL, succR) (ContractionR gamma delta a x) =
  error "TODO"
delPatchL f c ws@(anteL, anteR, succL, succR) (WeakeningL gamma delta a x) =
  error "TODO"
delPatchL f c ws@(anteL, anteR, succL, succR) (WeakeningR gamma delta a x) =
  error "TODO"
delPatchL f c ws@(anteL, anteR, succL, succR) (NegL gamma delta a x) =
  error "TODO"
delPatchL f c ws@(anteL, anteR, succL, succR) (NegR gamma delta a x) =
  error "TODO"
delPatchL f c ws@(anteL, anteR, succL, succR) (ConjL gamma delta a b x) =
  error "TODO"
delPatchL f c ws@(anteL, anteR, succL, succR) (ConjR gamma delta a b x1 x2) =
  error "TODO"
delPatchL f c ws@(anteL, anteR, succL, succR) (DisjL gamma delta a b x1 x2) =
  error "TODO"
delPatchL f c ws@(anteL, anteR, succL, succR) (DisjR gamma delta a b x) =
  error "TODO"
delPatchL f c ws@(anteL, anteR, succL, succR) (ImpL gamma delta a b x1 x2) =
  error "TODO"
delPatchL f c ws@(anteL, anteR, succL, succR) (ImpR gamma delta a b x) =
  error "TODO"

-- a -> (Q : (gamma ==> delta, a)) (R : (a, gamma ==> delta)) → (gamma ==> delta)
cutReduce :: Sentence -> Proof -> Proof -> Proof
cutReduce (Atom v) q r =
  -- q: gamma ==> delta, v
  -- r: v, gamma ==> delta
  let r1 = delPatchL fr (Atom v) ([], gamma, delta, []) r -- gamma, (gamma -* v) ==> delta, delta
      r2 = weakeningLto (gamma ++ gamma) r1 -- gamma, gamma ==> delta, delta
      r3 = contractDouble gamma delta r2 -- gamma ==> delta
  in
    r3
  where
    (gamma, _) = typeof q
    (_, delta) = typeof r
    
    -- _ -> _ -> (gamma ==> delta, v)
    fr :: [Proof] -> Proof -> Proof
    fr [] (Leaf _) = q

cutReduce (Neg b) q r =
  -- q: gamma ==> delta, (Neg b)
  -- r: (Neg b), gamma ==> delta
  let q1 = delPatchR fq (Neg b) ([], [b], [], []) q -- gamma, b ==> (delta -* Neg b)
      q2 = weakeningRto delta q1 -- gamma, b ==> delta
      q3 = exchangesAnteL [] gamma [] b q2 -- b, gamma ==> delta
      r1 = delPatchL fr (Neg b) ([], [], [b], []) r -- (gamma -* Neg b) ==> b, delta
      r2 = weakeningLto gamma r1 -- gamma ==> b, delta
      r3 = exchangesSuccR [] delta [] b r2 -- gamma ==> delta, b
  in
    Cut gamma delta b r3 q3
  where
    (gamma, _) = typeof q
    (_, delta) = typeof r
    -- (gamma ==> delta, (Neg b)) → (gamma, b ==> (delta -* Neg b))
    fq :: [Proof] -> Proof -> Proof
    fq [x1] (NegR gamma delta _ _) =
      -- x1: b, gamma, b ==> (delta -* Neg b)
      -- want: gamma, b ==> (delta -* Neg b)
      let x2 = exchangesAnteL [b] gamma [] b x1 -- b, b, gamma ==> (delta -* Neg b)
          x3 = contractionL x2 -- b, gamma ==> (delta -* Neg b)
          x4 = exchangesAnteR [] gamma [] b x3 -- gamma, b ==> (delta -* Neg b)
      in
        x4
    
    fr :: [Proof] -> Proof -> Proof
    fr [x1] (NegR gamma delta _ _) =
      error "TODO"

cutReduce (Conj b c) q r =
  -- q: gamma ==> delta, (Conj b c)
  -- r: (Conj b c), gamma ==> delta
  let qc1 = delPatchR fqc (Conj b c) ([], [], [], [c]) q -- gamma ==> (delta -* (Conj b c)), c
      qb1 = delPatchR fqb (Conj b c) ([], [], [], [b]) q -- gamma ==> (delta -* (Conj b c)), b
      r1 = delPatchL fr (Conj b c) ([b, c], [], [], []) r -- b, c, (gamma -* (Conj b c)) ==> delta
      qc2 = weakeningRto (delta ++ [c]) qc1 -- gamma ==> delta, c
      qb2 = weakeningRto (delta ++ [b]) qb1 -- gamma ==> delta, b
      qb3 = weakeningL c qb2 -- c, gamma ==> delta, b
      r2 = weakeningLto (b : c : gamma) r1 -- b, c, gamma ==> delta
      qr1 = cut qb3 r2 -- c, gamma ==> delta
      qr2 = cut qc2 qr1 -- gamma ==> delta
  in
    qr2
  where
    (gamma, _) = typeof q
    (_, delta) = typeof r

    fqc :: [Proof] -> Proof -> Proof
    fqc [x, y] (ConjR gamma delta _ _ _ _) =
      -- x: gamma ==> (delta -* Conj b c), b, c
      -- y: gamma ==> (delta -* Conj b c), c, c
      -- want: gamma ==> (delta -* Conj b c), c
      contractionR y
    
    fqb :: [Proof] -> Proof -> Proof
    fqb [x, y] (ConjR gamma delta _ _ _ _) =
      -- x: gamma ==> (delta -* Conj b c), b, b
      -- y: gamma ==> (delta -* Conj b c), c, b
      -- want: gamma ==> (delta -* Conj b c), b
      contractionR x
    
    fr :: [Proof] -> Proof -> Proof
    fr = error "TODO"

cutReduce (Disj b c) q r =
  -- q: gamma ==> delta, (Disj b c)
  -- r: (Disj b c), gamma ==> delta
  error "TODO"
  where
    (gamma, _) = typeof q
    (_, delta) = typeof r

cutReduce (Imp b c) q r =
  -- q: gamma ==> delta, (Imp b c)
  -- r: (Imp b c), gamma ==> delta
  error "TODO"
  where
    (gamma, _) = typeof q
    (_, delta) = typeof r

cutReduceS :: Sentence -> ProofS -> ProofS -> ProofS
cutReduceS s p1 p2 = simplify (cutReduce s (expand p1) (expand p2))


-- Given a proof of greatest cut depth d+1, lower the max cut to depth d
cutLower :: Int -> Proof -> Proof
cutLower d = expand . cutLowerS d . simplify

cutLowerS :: Int -> ProofS -> ProofS
cutLowerS d =
  foldProofSS $ \ rl cs ss ps rs ->
  -- if rl == RuleCut then ss = [a] for some a
  if rl == RuleCut && succ d == dp (head ss) then
    let [a] = ss
        [x1, x2] = rs in -- TODO: = rs or = ps?
      cutReduceS a x1 x2
  else
    ProofS rl cs ss rs


cutElim :: Proof -> Proof
cutElim p = h p (maxCutDepth p) where
  h :: Proof -> Int -> Proof
  h p 0 = p
  h p d1 = let d = pred d1 in h (cutLower d p) d

cutElimS :: ProofS -> ProofS
cutElimS = simplify . cutElim . expand

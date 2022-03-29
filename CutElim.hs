module CutElim where
import Types
import Helpers

deleteDAs :: Sentence -> Cedent -> Cedent
deleteDAs = filter . (/=)

infix 9 -*
(-*) :: Cedent -> Sentence -> Cedent
(-*) = flip deleteDAs

-- Assumes that c is not in anteL, anteR, succL, or succR, and that it is not atomic
-- f -> c -> (gamma ==> delta) -> (anteL, gamma, anteR ==> succL, (delta -* c), succR)
-- First arg (f) is a special case for when delPatchR'ing with c = (Neg ...) and the
-- rule NegR, or c = (Conj ...) and ConjL, etc. It takes the delPatchR'd proof and the
-- original proof and returns what to do in this special case
-- See pp. 38-39 in Buss' Handbook of Proof Theory, ch. 1
delPatchR :: ([Proof] -> Proof -> Proof) -> Sentence -> (Cedent, Cedent, Cedent, Cedent) -> Proof -> Proof
delPatchR f c ws@(anteL, anteR, succL, succR) (Leaf a) =
  -- want: anteL, a, anteR ==> succL, ([Atom a] -* c), succR
  let x1 = Leaf a -- a ==> a
      x2 = weakenings ws x1 -- anteL, a, anteR ==> succL, a, succR
  in -- c is not atomic, so (c /= Atom a) and thus ([Atom a] -* c = [Atom a])
    x2
delPatchR f c ws@(anteL, anteR, succL, succR) (Cut gamma delta a x y) =
  -- x: gamma ==> delta, a
  -- y: a, gamma ==> delta
  -- want: anteL, gamma, anteR ==> succL, (delta -* c), succR
  if c == a then
    delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), succR
  else
    let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), a, succR
        x2 = exchangesSuccR (anteL ++ gamma ++ anteR) [] (succL ++ (delta -* c)) succR a x1 -- anteL, gamma, anteR ==> a, succL, (delta -* c), succR
        y1 = delPatchR f c ws y -- anteL, a, gamma, anteR ==> succL, (delta -* c), succR
        y2 = exchangesAnteL [] anteL (gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a y1 -- anteL, gamma, anteR, a ==> succL, (delta -* c), succR
    in
      Cut (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a x2 y2
delPatchR f c ws@(anteL, anteR, succL, succR) (ExchangeL gamma delta pi a b x) =
  -- x: gamma, a, b, delta ==> pi
  -- want: anteL, gamma, b, a, delta, anteR ==> succL, (pi -* c), succR
  let x1 = delPatchR f c ws x -- anteL, gamma, a, b, delta, anteR ==> succL, (pi -* c), succR
      x2 = ExchangeL (anteL ++ gamma) (delta ++ anteR) (succL ++ (pi -* c) ++ succR) a b -- anteL, gamma, b, a, delta, anteR ==> succL, (pi -* c), succR
  in
    x2
delPatchR f c ws@(anteL, anteR, succL, succR) (ExchangeR gamma delta pi a b x) =
  -- x: gamma ==> delta, a, b, pi
  -- want: anteL, gamma, anteR ==> succL, ((delta, b, a, pi) -* c), succR
  if c == a || c == b then
    delPatchR f c ws x -- No need to exchange a and b because one/both get deleted
  else
    let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), a, b, (pi -* c), succR
        x2 = ExchangeR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) ((pi -* c) ++ succR) a b -- anteL, gamma, anteR ==> succL, (delta -* c), b, a (pi -* c), succR
    in
      x2
delPatchR f c ws@(anteL, anteR, succL, succR) (ContractionL gamma delta a x) =
  -- x: a, a, gamma ==> delta
  -- want: anteL, a, gamma, anteR ==> succL, (delta -* c), succR
  let x1 = delPatchR f c ws x -- anteL, a, a, gamma, anteR ==> succL, (delta -* c), succR
      x2 = exchangesAnteL [] anteL (a : gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a x1 -- a, anteL, a, gamma, anteR ==> succL, (delta -* c), succR
      x3 = exchangesAnteL [a] anteL (gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a x2 -- a, a, anteL, gamma, anteR ==> succL, (delta -* c), succR
      x4 = ContractionL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a x3 -- a, anteL, gamma, anteR ==> succL, (delta -* c), succR
      x5 = exchangesAnteR [] anteL (gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a x4 -- anteL, a, gamma, anteR ==> succL, (delta -* c), succR
  in
    x5
delPatchR f c ws@(anteL, anteR, succL, succR) (ContractionR gamma delta a x) =
  -- x: gamma ==> delta, a, a
  -- want: anteL, gamma, anteR ==> succL, (delta -* c), (a -* c), succR
  if c == a then
    delPatchR f c ws x -- no need to contract because a was deleted
  else
    let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), a, a, succR
        x2 = exchangesSuccR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ [a]) succR [] a x1 -- anteL, gamma, anteR ==> succL, (delta -* c), a, succR, a
        x3 = exchangesSuccR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [a] a x2 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a, a
        x4 = ContractionR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a x3 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a
        x5 = exchangesSuccL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [] a x4 -- anteL, gamma, anteR ==> succL, (delta -* c), a, succR
    in
      x5
delPatchR f c ws@(anteL, anteR, succL, succR) (WeakeningL gamma delta a x) =
  -- x: gamma ==> delta
  -- want: anteL, a, gamma, anteR ==> succL, (delta -* c), succR
  let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), succR
      x2 = WeakeningL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a x1 -- a, anteL, gamma, anteR ==> succL, (delta -* c), succR
      x3 = exchangesAnteR [] anteL (gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a x2 -- anteL, a, gamma, anteR ==> succL, (delta -* c), succR
  in
    x3
delPatchR f c ws@(anteL, anteR, succL, succR) (WeakeningR gamma delta a x) =
  -- x: gamma ==> delta
  -- want: anteL, gamma, anteR ==> succL, (delta -* c), (a -* c), succR
  if c == a then
    delPatchR f c ws x -- no need to weaken because a was deleted
  else
    let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), succR
        x2 = WeakeningR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a x1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a
        x3 = exchangesSuccL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [] a x2 -- anteL, gamma, anteR ==> succL, (delta -* c), a, succR
    in
      x3
delPatchR f c ws@(anteL, anteR, succL, succR) (NegL gamma delta a x) =
  -- x: gamma ==> delta, a
  -- want: anteL, (Neg a), gamma, anteR ==> succL, (delta -* c), succR
  if c == a then
    let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), succR
        x2 = WeakeningL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) (Neg a) x1 -- (Neg a), anteL, gamma, anteR ==> succL, (delta -* c), succR
        x3 = exchangesAnteR [] anteL (gamma ++ anteR) (succL ++ (delta -* c) ++ succR) (Neg a) x2 -- anteL, (Neg a), gamma, anteR ==> succL, (delta -* c), succR
    in
      x3
  else
    let x1 = delPatchR f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), a, succR
        x2 = exchangesSuccR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [] a x1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a
        x3 = NegL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a x2 -- (Neg a), anteL, gamma, anteR ==> succL, (delta -* c), succR
        x4 = exchangesAnteR [] anteL (gamma ++ anteR) (succL ++ (delta -* c) ++ succR) (Neg a) x3 -- anteL, (Neg a), gamma, anteR ==> succL, (delta -* c), succR
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
        x2 = exchangesAnteL [] anteL (gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a x1 -- a, anteL, gamma, anteR ==> succL, (delta -* c), succR
        x3 = NegR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Neg a)
        x4 = exchangesSuccL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [] (Neg a) x3 -- anteL, gamma, anteR ==> succL, (delta -* c), (Neg a), succR
    in
      x4
delPatchR f c ws@(anteL, anteR, succL, succR) (ConjL gamma delta a b x) =
  -- x: a, b, gamma ==> delta
  -- want: anteL, (Conj a b), gamma, anteR ==> succL, (delta -* c), succR
  let x1 = delPatchR f c ws x -- anteL, a, b, gamma, anteR ==> succL, (delta -* c), succR
      x2 = exchangesAnteL [] anteL (b : gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a x1 -- a, anteL, b, gamma, anteR ==> succL, (delta -* c), succR
      x3 = exchangesAnteL [a] anteL (gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a x2 -- a, b, anteL, gamma, anteR ==> succL, (delta -* c), succR
      x4 = ConjL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a b x3 -- (Conj a b), anteL, gamma, anteR ==> succL, (delta -* c), succR
      x5 = exchangesAnteR [] anteL (gamma ++ anteR) (succL ++ (delta -* c) ++ succR) (Conj a b) x4 -- anteL, (Conj a b), gamma, anteR ==> succL, (delta -* c), succR
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
        let x2 = WeakeningR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) (Conj a b) x1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Conj a b)
            x3 = exchangesSuccL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [] (Conj a b) x2 -- anteL, gamma, anteR ==> succL, (delta -* c), (Conj a b), succR
        in
          x3
      else if c == b then
        let y2 = WeakeningR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) (Conj a b) y1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Conj a b)
            y3 = exchangesSuccL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [] (Conj a b) y2 -- anteL, gamma, anteR ==> succL, (delta -* c), (Conj a b), succR
        in
          y3
      else
        let x2 = exchangesSuccR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [] a x1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a
            y2 = exchangesSuccR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [] b y1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, b
            z1 = ConjR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a b x2 y2 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Conj a b)
            z2 = exchangesSuccL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [] (Conj a b) z1 -- anteL, gamma, anteR ==> succL, (delta -* c), (Conj a b), succR
        in
          z2
delPatchR f c ws@(anteL, anteR, succL, succR) (DisjL gamma delta a b x y) =
  -- x: a, gamma ==> delta
  -- y: b, gamma ==> delta
  -- want: anteL, (Disj a b), gamma, anteR ==> succL, (delta -* c), succR
  let x1 = delPatchR f c ws x -- anteL, a, gamma, anteR ==> succL, (delta -* c), succR
      y1 = delPatchR f c ws y -- anteL, b, gamma, anteR ==> succL, (delta -* c), succR
      x2 = exchangesAnteL [] anteL (gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a x1 -- a, anteL, gamma, anteR ==> succL, (delta -* c), succR
      y2 = exchangesAnteL [] anteL (gamma ++ anteR) (succL ++ (delta -* c) ++ succR) b y1 -- b, anteL, gamma, anteR ==> succL, (delta -* c), succR
      z1 = DisjL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a b x2 y2 -- (Disj a b), anteL, gamma, anteR ==> succL, (delta -* c), succR
      z2 = exchangesAnteR [] anteL (gamma ++ anteR) (succL ++ (delta -* c) ++ succR) (Disj a b) z1 -- anteL, (Disj a b), gamma, anteR ==> succL, (delta -* c), succR
  in
    z2
delPatchR f c ws@(anteL, anteR, succL, succR) (DisjR gamma delta a b x) =
  -- x: gamma ==> delta, a, b
  -- want: anteL, gamma, anteR ==> succL, (delta -* c), (Disj a b -* c), succR
  let x1 = delPatch f c ws x -- anteL, gamma, anteR ==> succL, (delta -* c), (a -* c), (b -* c), succR
  in
    if c == Disj a b then
      f [x1] (DisjR gamma delta a b x)
    else
      if c == a && c == b then
        let x2 = WeakeningR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) (Disj a b) x1 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Disj a b)
            x3 = exchangesSuccL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [] (Disj a b) x2 -- anteL, gamma, anteR ==> succL, (delta -* c), (Disj a b), succR
        in
          x3
      else if c == a then
        let x2 = WeakeningR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ b : succR) a x1 -- anteL, gamma, anteR ==> succL, (delta -* c), b, succR, a
            x3 = exchangesSuccR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) (succR ++ [a]) [] b x2 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a, b
            x4 = DisjR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a b x3 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Disj a b)
            x5 = exchangesSuccL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [] (Disj a b) x4 -- anteL, gamma, anteR ==> succL, (delta -* c), (Disj a b), succR
        in
          x5
      else if c == b then
        let x2 = WeakeningR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ a : succR) b x1 -- anteL, gamma, anteR ==> succL, (delta -* c), a, succR, b
            x3 = exchangesSuccR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [b] a x2 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a, b
            x4 = DisjR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a b x3 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Disj a b)
            x5 = exchangesSuccL (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [] (Disj a b) x4 -- anteL, gamma, anteR ==> succL, (delta -* c), (Disj a b), succR
        in
          x5
      else
        let x2 = exchangesSuccR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ [a]) succR [] b x1 -- anteL, gamma, anteR ==> succL, (delta -* c), a, succR, b
            x3 = exchangesSuccR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c)) succR [b] a x2 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, a, b
            x4 = DisjR (anteL ++ gamma ++ anteR) (succL ++ (delta -* c) ++ succR) a b x3 -- anteL, gamma, anteR ==> succL, (delta -* c), succR, (Disj a b)
            x5 = exchangesSuccL (anteL ++ gamma ++ anteR)
        in
          x8
delPatchR f c ws@(anteL, anteR, succL, succR) (ImpL gamma delta a b x y) =
  error "TODO"
delPatchR f c ws@(anteL, anteR, succL, succR) (ImpR gamma delta a b x) =
  error "TODO"

-- f -> c -> (gamma ==> delta) -> (anteL, (gamma -* c), anteR ==> succL, delta, succR)
delPatchL :: (Proof -> Proof -> Proof) -> Sentence -> (Cedent, Cedent, Cedent, Cedent) -> Proof -> Proof
delPatchL f c ws@(anteL, anteR, succL, succR) (Leaf a) =
  -- want: anteL, (a -* c), anteR ==> succL, a, succR
  let x1 = Leaf a -- a ==> a
      x2 = weakenings ws x1 -- anteL, a, anteR ==> succL, a, succR
  in -- c is not atomic, so (c /= Atom a) and thus (a -* c = a)
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
  error "TODO"
  where
    (gamma, _) = typeof q
    (_, delta) = typeof r

cutReduce (Neg b) q r =
  -- q: gamma ==> delta, (Neg b)
  -- r: (Neg b), gamma ==> delta
  let q1 = delPatchR fq (Neg b) ([], [b], [], []) q -- gamma, b ==> (delta -* Neg b)
      q2 = weakeningRto delta q1 -- gamma, b ==> delta
      q3 = exchangesAnteL [] gamma [] delta b q q2 -- b, gamma ==> delta
      r1 = delPatchL fr (Neg b) ([], [], [b], []) r -- (gamma -* Neg b) ==> b, delta
      r2 = weakeningLto gamma r1 -- gamma ==> b, delta
      r3 = exchangesSuccR gamma [] delta [] b r2 -- gamma ==> delta, b
  in
    Cut gamma delta b r3 q3
  where
    (gamma, _) = typeof q
    (_, delta) = typeof r
    -- (gamma ==> delta, (Neg b)) → (gamma, b ==> (delta -* Neg b))
    fq :: [Proof] -> Proof -> Proof
    fq [x1] (NegR gamma delta _ _) =
      -- x1: b, gamma, b ==> (delta -* c)
      -- want: gamma, b ==> (delta -* c)
      let x2 = exchangesAnteL [b] gamma [] (delta -* c) b x1 -- b, b, gamma ==> (delta -* c)
          x3 = ContractionL gamma (delta -* c) b x2 -- b, gamma ==> (delta -* c)
          x4 = exchangesAntesR [] gamma [] (delta -* c) b x3 -- gamma, b ==> (delta -* c)
      in
        x4
    
    fr :: [Proof] -> Proof -> Proof
    fr [x1] (NegR gamma delta _ _) =
      error "TODO"

cutReduce (Conj b c) q r =
  -- q: gamma ==> delta, (Conj b c)
  -- r: (Conj b c), gamma ==> delta
  let qc1 = delPatchR fqc (Conj b c) ([], [], [], [c]) -- gamma ==> (delta -* (Conj b c)), c
      qb1 = delPatchR fcb (Conj b c) ([], [], [], [b]) -- gamma ==> (delta -* (Conj b c)), b
      r1 = delPatchL fr (Conj b c) ([b, c], [], [], []) -- b, c, (gamma -* (Conj b c)) ==> delta
      qc2 = weakenRto (delta ++ [c]) qc1 -- gamma ==> delta, c
      qb2 = weakenRto (delta ++ [b]) qb1 -- gamma ==> delta, b
      qb3 = WeakeningL gamma (delta ++ [b]) c -- c, gamma ==> delta, b
      r2 = weakenLto (b : c : gamma) r1 -- b, c, gamma ==> delta
      qr1 = Cut (c : gamma) delta b qb3 r2 -- c, gamma ==> delta
      qr2 = Cut gamma delta c qc2 qr1 -- gamma ==> delta
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
      ContractionR gamma (delta -* Conj b c) c y
    
    fqb :: [Proof] -> Proof -> Proof
    fqb [x, y] (ConjR gamma delta _ _ _ _) =
      -- x: gamma ==> (delta -* Conj b c), b, b
      -- y: gamma ==> (delta -* Conj b c), c, b
      -- want: gamma ==> (delta -* Conj b c), b
      ContractionR gamma (delta -* Conj b c) b x
    
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
cutReduceS s p1 p2 = cutReduce s (expand p1) (expand p2)


-- Given a proof of greatest cut depth d+1, lower the max cut to depth d
cutLower :: Int -> Proof -> Proof
cutLower d = expand . cutLowerS d . simplify

cutLowerS :: Int -> ProofS -> ProofS
cutLowerS d =
  foldProofSS $ \ rl cs ss ps rs ->
  if rl == RuleCut && succ d == proofDepthS (ProofS rl cs ss ps) then
    let [x1, x2] = ps in cutReduceS a x1 x2
  else
    ProofS rl cs ss rs


cutElim :: Proof -> Proof
cutElim p = h p (maxCutDepth p) where
  h :: Proof -> Int -> Proof
  h p 0 = p
  h p d1 = let d = pred d1 in h (cutLower d p) d

cutElimS :: ProofS -> ProofS
cutElimS = simplify . cutElim . expand

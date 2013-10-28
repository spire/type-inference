> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, KindSignatures, TemplateHaskell,
>       FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
>       UndecidableInstances, GeneralizedNewtypeDeriving,
>       TypeSynonymInstances, ScopedTypeVariables #-}

This module defines test cases for the unification algorithm, divided
into those which must succeed, those which should block (possibly
succeeding partially), and those which must fail.

> module PatternUnify.Test where

> import Control.Applicative
> import Control.Arrow ((+++))
> import Control.Monad (unless)
> import Data.Foldable (foldMap)

> import Unbound.LocallyNameless

> import Common.BwdFwd
> import Common.PrettyPrint
> import PatternUnify.Tm
> import PatternUnify.Context
> import PatternUnify.Check
> import PatternUnify.Unify

> if' :: String -> Type -> Tm -> Tm -> Tm -> Tm
> if' s b x t f = x %% If (bind (s2n s) b) t f

> if'' :: Type -> Tm -> Tm -> Tm -> Tm
> if'' = if' "_x"

> fold' :: String -> Type -> Tm -> String -> String -> Tm -> Tm -> Tm
> fold' x _P cz y z cs n = n %% Fold (bind (s2n x) _P) cz (bind (s2n y) (bind (s2n z) cs))

> fold'' :: Type -> Tm -> String -> Tm -> Tm -> Tm
> fold'' _C cz ih cs n = fold' "_x" _C cz "_y" ih cs n

> (&&&) :: Tm -> Tm -> Tm
> x &&& y = if'' BOOL x y FALSE

> ($$$) :: Tm -> [Tm] -> Tm
> ($$$) = foldl ($$)


> data TestType = Succeed | Stuck | Fail


Allocate a fresh name so the counter starts from 1, to avoid clashing
with s2n (which generates names with index 0):

> initialise :: Contextual ()
> initialise = (fresh (s2n "init") :: Contextual (Name Tm)) >> return ()

> unify :: [Entry] -> Either String [Entry]
> unify ezs = id +++ (fwd . fst . snd) $
>             -- Using a non-empty params (the 'B0') here results in all
>             -- memory consumed! However, we put the Spire context in the
>             -- params of each problem we create, so we shouldn't need
>             -- a non-empty params here.
>             runContextual (bwd ezs) B0 $
>             do initialise
>                normalize
>                ambulando []
>                validate ()
>                checkHolds (probs ezs)
>   where
>     probs = foldMap foo
>     foo (E _ _) = []
>     foo (Q _ p) = [p]

Normalize the equations w.r.t. the DEFNs:
- substitute all DEFNs into all equations.
Check that the input is well-formed along the way:
- meta context is entirely on the left.
- problems and metavars are in dependency order.
- problems are active.
Side effect: meta context moves from left to right.

>     -- Based on 'PatternUnify.Check.validate'.
>     normalize = do
>       _Del' <- getR
>       unless (null _Del') $ error "normalize: not at far right"
>       n =<< getL
>       putL B0
>       where
>         n :: ContextL -> Contextual ()
>         n B0 = return ()
>         n (_Del :< E x _) | x <? _Del =
>           error $ "normalize: dependency error: " ++ show x ++
>                   " occurs before its declaration"
>         n (_ :< p@(Q state _)) | state /= Active =
>           error $ "normalize: non-active problem: " ++ show p
>         n (_Del :< e@(E x (_ , DEFN v))) = do
>           -- Set up a delayed substitution.
>           pushR . Left $ [(x , v)]
>           pushR . Right $ e
>           n _Del
>         n (_Del :< e) = do
>           pushR . Right $ e
>           n _Del


The |test| function executes the constraint solving algorithm on the
given metacontext.

> test :: TestType -> [Entry] -> IO ()
> test tt ezs = do
>     putStrLn $ "\n\nInitial context:\n" ++ pp ezs
>     let r = PatternUnify.Test.unify ezs
>     case (r, tt) of
>         (Left err,  Fail)  -> putStrLn $ "OKAY: expected failure:\n" ++ err
>         (Right x,   Fail)  -> putStrLn $ "FAIL: unexpected success:\n" ++ showX x
>         (Left err,  _)     -> putStrLn $ "FAIL: unexpected failure:\n" ++ err
>         (Right x,   Succeed) | succeeded x  -> do putStrLn $ "OKAY: succeeded:\n" ++ showX x
>                              | otherwise    -> putStrLn $ "FAIL: did not succeed:\n" ++ showX x
>         (Right x,   Stuck)   | succeeded x  -> putStrLn $ "FAIL: did not get stuck:\n" ++ showX x
>                              | otherwise    -> putStrLn $ "OKAY: stuck:\n" ++ showX x
>   where
>     showX cxL = "Final context:\n" ++ pp cxL
>     succeeded cxL = not (anyBlocked cxL)

> runTestSolved, runTestStuck, runTestFailed, patternUnify :: IO ()
> runTestSolved = mapM_ (test Succeed) tests
> runTestStuck  = mapM_ (test Stuck) stucks
> runTestFailed = mapM_ (test Fail) fails
> patternUnify = runTestSolved >> runTestStuck >> runTestFailed

> lifted :: Nom -> Type -> [Entry] -> [Entry]
> lifted x _T es = lift [] es
>    where
>      lift :: Subs -> [Entry] -> [Entry]
> -- We expect to also need to substitute into definitions.
> -- For now, we restrict ourselves to holes without definitions.
>      lift g (E a (_A, HOLE) : as)  = E a (_Pi x _T (substs g _A), HOLE) :
>                                          lift ((a, meta a $$ var x) : g) as
>      lift g (Q s p : as)        = Q s (allProb x _T (substs g p)) : lift g as
>      lift _ [] = []

> -- Adds a universal quantifier using 'lifted' for skolemization
> -- (pushing the universal under existentials), and binding it
> -- in front of a group of universals in problems.
> boy :: String -> Type -> [Entry] -> [Entry]
> boy = lifted . s2n

> -- Adds an existential quantifier.
> gal :: String -> Type -> Entry
> gal x _T = E (s2n x) (_T, HOLE)

> eq :: String -> Type -> Tm -> Type -> Tm -> Entry
> eq x _S s _T t = Q Active $ Unify $ EQN _S s _T t



Testing:

    PatternUnify.Test.unify (tests !! 1)

> tests, stucks, fails :: [[Entry]]
> tests = [ 

-- >           ( boy "T" TYPE
-- >             [ gal "P" (vv "T" --> TYPE)
-- >             , gal "A" (vv "T" --> TYPE)
-- >             , gal "B" (_PI "x" (vv "T") ((mv "A" $$ vv "x") --> TYPE))
-- >             ] ++
-- >             ( boy "x" (vv "T")
-- >               [ eq "p" TYPE (mv "P" $$ vv "x")
-- >                        TYPE (_PI "y" (mv "A" $$ vv "x") (mv "B" $$$ [vv "x" , vv "y"]))
-- >               ]
-- >             )
-- >           )

>           -- A 'forcePi' problem with no term variables:
>           --
>           --   ?P == Pi y:?A. ?B y
>           [ gal "P" TYPE
>           , gal "A" TYPE
>           , gal "B" (mv "A" --> TYPE)
>           ] ++
>           [ eq "p" TYPE (mv "P")
>                    TYPE (_PI "y" (mv "A") (mv "B" $$$ [vv "y"]))
>           ]

unify': before: [
?12 : Type := Type
,?13 : Type -> Type
,?9 : Type := Pi (_forcePi : Type) (??13 _forcePi)
,?8 : Pi (_forcePi : Type) (??13 _forcePi)
,?18 : Type -> Type
,?19 : Pi (_ : Type) (??18 _ -> Type)

,?Active (_ : Type) -> (x : _) -> (??13 _ : Type) == (Pi (_forcePi : ??18 _) (??19 _ _forcePi) : Type)]

?13 : Type -> Type
?18 : Type -> Type
?19 : (T : Type) -> (?18 T) -> Type
equation:
  forall T : Type. forall (x : T). ?13 T == (x : ?18 T) -> (?19 T x)

>         , [ gal "P" (TYPE --> TYPE)
>           , gal "A" (TYPE --> TYPE)
>           , gal "B" (_PI "T" TYPE ((mv "A" $$ vv "T") --> TYPE))
>           ] ++
>           boy "T" TYPE ( boy "x" (vv "T") [
>             eq "p" TYPE (mv "P" $$ vv "T")
>                    TYPE (_PI "y" (mv "A" $$ vv "T") (mv "B" $$$ [vv "T" , vv "y"]))])


>           -- A 'forcePi' problem with term variables:
>           --
>           --   T : Type
>           --   x : T
>           --   |-
>           --   ?P x == Pi y:?A x. ?B x y
>         , ( boy "T" TYPE
>             [ gal "P" TYPE
>             , gal "A" TYPE
>             , gal "B" (mv "A" --> TYPE)
>             ] ++
>             ( boy "x" (vv "T")
>               [ eq "p" TYPE (mv "P" $$ vv "x")
>                        TYPE (_PI "y" (mv "A" $$ vv "x") (mv "B" $$$ [vv "x" , vv "y"]))
>               ]
>             )
>           )

XXX: broken example: was trying to see if fixing the domain of the RHS
helped, since I think I can actually do that, following Matita.

Use e.g.

    PatternUnify.Test.unify (tests !! 2)

to test the tests in the GHCI prompt. Use e.g.

    pp (tests !! 2)

to see what you're testing.

  P : Type -> Type,
  B : Type -> Bool -> Type,
  ?Active (x : T) ->
    (?P x : Type) == (Pi (y : Bool) (?B x y) : Type)

>         , ( boy "T" TYPE
>             [ gal "P" TYPE
>             , gal "B" (BOOL --> TYPE)
>             ] ++
>             ( boy "x" (vv "T")
>               [ eq "p" TYPE (mv "P" $$ vv "x")
>                        TYPE (_PI "y" BOOL (mv "B" $$$ [vv "x" , vv "y"]))
>               ]
>             )
>           )

This seems to be the reflexive equality which fails as part of the
previous test, but here it succeeds ???!!! NO!!! The one above is
ill-typed!!! See below for another try.

  B : Type -> Bool -> Type,
  ?Active (x : Type) ->
    (Pi (y : Bool) (?B x y) : Type) == (Pi (y : Bool) (?B x y) : Type)

>         , ( boy "x" TYPE
>             [ gal "B" (BOOL --> TYPE)
>             , eq "p" TYPE (_PI "y" BOOL (mv "B" $$ vv "y"))
>                      TYPE (_PI "y" BOOL (mv "B" $$ vv "y"))
>             ]
>           )

>         , [ gal "P" (TYPE --> TYPE)
>           , gal "B" (TYPE --> BOOL --> TYPE)
>           ] ++
>           ( boy "T" TYPE
>             ( boy "x" (vv "T")
>               [ eq "p" TYPE (mv "P" $$ vv "T")
>                        TYPE (_PI "y" BOOL (mv "B" $$$ [vv "T" , vv "y"]))
>               ]
>             )
>           )

-- >         , ( boy "x" BOOL
-- >             [ gal "A" (TYPE --> TYPE)
-- >             , eq "p" TYPE (mv "A" --> mv "A")
-- >                      TYPE (mv "A" --> mv "A")
-- >             ]
-- >           )

>           -- test 0: solve B with A
>         , ( gal "A" TYPE
>           : gal "B" TYPE
>           : eq "p" TYPE (mv "A") TYPE (mv "B")
>           : [])

>           -- test 1: solve B with \ _ . A
>         , let _P = _SIG "b2" BOOL (if'' TYPE (vv "b2") BOOL BOOL)
>               _T = NAT --> _P
>               _F = _T --> NAT
>           in
>           ( gal "F1" _F : gal "F2" _F : eq "p" _F (mv "F1") _F (mv "F2") : [])

>           -- test 1: solve B with \ _ . A
>         , ( gal "A" BOOL
>           : gal "B" (BOOL --> BOOL)
>           : boy "x" BOOL 
>             ( eq "p" BOOL (mv "A") BOOL (mv "B" $$ vv "x")
>             : [])
>           )

>           -- test 2: restrict B to second argument
>         , ( gal "A" TYPE
>           : gal "B" (mv "A" --> mv "A" --> BOOL)
>           : eq "p" (mv "A" --> mv "A" --> BOOL)
>                        (lam (s2n "x") (lam (s2n "y") (mv "B" $$$ [vv "y", vv "x"])))
>                    (mv "A" --> mv "A" --> BOOL)
>                        (lam (s2n "x") (lam (s2n "y") (mv "B" $$$ [vv "x", vv "x"])))
>           : [])

>           -- test 3: X unchanged
>         , [ gal "X" (_PI "A" BOOL (if'' TYPE (vv "A") BOOL BOOL --> BOOL)) 
>           , eq "p" BOOL (mv "X" $$$ [TRUE, TRUE])
>                    BOOL (mv "X" $$$ [TRUE, TRUE])
>           ]

>           -- test: dingo
>         , [ gal "X" (_PI "N" NAT (fold'' TYPE BOOL "IH" (vv "IH") (vv "N") --> BOOL)) 
>           , eq "p" BOOL (mv "X" $$$ [ZE, TRUE])
>                    BOOL (mv "X" $$$ [ZE, TRUE])
>           ]

>           -- test: dingo
>         , [ gal "X" (_PI "N" NAT (fold'' TYPE BOOL "IH" (vv "IH") (vv "N") --> BOOL)) 
>           , eq "p" BOOL (mv "X" $$$ [SU ZE, FALSE])
>                    BOOL (mv "X" $$$ [SU ZE, FALSE])
>           ]


>           -- test: unify ?X : set against set : set
>         , [ gal "Z" TYPE
>           , eq "p" TYPE (mv "Z") TYPE TYPE
>           ]


>  -- The type inference problem here is that Bool has type Z.
>  -- We hope to learn what Z is TYPE from this.
>  --           -- test 3 + 1/3:
>  --         , [ gal "Z" TYPE
>  --           , gal "X" (_PI "A" BOOL (if'' (mv "Z") (vv "A") BOOL BOOL --> BOOL))
>  --           , eq "p" BOOL (mv "X" $$$ [TRUE, TRUE])
>  --                    BOOL (mv "X" $$$ [TRUE, TRUE])
>  --           ]

>           -- test 4: solve A with BOOL
>         , [ gal "A" TYPE
>           , eq "p" TYPE (mv "A") TYPE BOOL
>           ]

>           -- test 5: solve A with B -> B
>         , [ gal "A" TYPE
>           , gal "B" TYPE
>           , gal "C" TYPE
>           , eq "p" TYPE (mv "A") TYPE (mv "B" --> mv "B")
>           ]

>           -- test 6: solve A with \ X . B && X
>         , ( gal "A" (BOOL --> BOOL) 
>           : gal "B" BOOL
>           : boy "X" BOOL
>             ( eq "p" BOOL (mv "A" $$ vv "X") BOOL (mv "B" &&& vv "X")
>             : [])
>           )

>           -- test 7: solve A with \ _ X _ . B X &&& X
>         , ( gal "A" (BOOL --> BOOL --> BOOL --> BOOL)
>           : gal "B" (BOOL --> BOOL)
>           : boy "X" BOOL
>             ( boy "Y" BOOL
>               (eq "p" BOOL (mv "A" $$$ [vv "Y", vv "X", vv "Y"])
>                       BOOL (mv "B" $$ vv "X" &&& vv "X")
>               : [])
>             )
>           )

>           -- test 8: solve S with A and T with B
>         , [ gal "A" TYPE
>           , gal "S" TYPE
>           , gal "B" (mv "A" --> BOOL)
>           , gal "T" (mv "S" --> BOOL)
>           , eq "p" (mv "A" --> BOOL) (ll "x" (mv "B" $$ vv "x"))
>                    (mv "S" --> BOOL) (ll "x" (mv "T" $$ vv "x"))
>           , eq "q" TYPE (mv "A") TYPE (mv "S")
>           ]

>           -- test 9: solve M with \ y . y
>         , [ gal "M" (BOOL --> BOOL)
>           , eq "p" (BOOL --> BOOL) (ll "y" (vv "y"))
>                    (BOOL --> BOOL) (ll "y" (mv "M" $$ vv "y"))
>           ]

>           -- test 10: solve A with \ _ X _ . X &&& X and B with \ X _ _ . X &&& X
>         , ( gal "A" (BOOL --> BOOL --> BOOL --> BOOL)
>           : boy "X" BOOL
>             ( boy "Y" BOOL
>               ( gal "B" (BOOL --> BOOL)
>               : eq "q" BOOL (mv "A" $$$ [vv "Y", vv "X", vv "Y"])
>                        BOOL (mv "B" $$ vv "Y")
>               : eq "p" BOOL (mv "A" $$$ [vv "Y", vv "X", vv "Y"])
>                        BOOL (vv "X" &&& vv "X")
>               : [])
>             )
>           )

>           -- test 11: solve A with \ _ y . y
>         , [ gal "A" (_PI "X" BOOL (if'' TYPE (vv "X") NAT BOOL --> if'' TYPE (vv "X") NAT BOOL))
>           , eq "p" (_PI "X" BOOL (if'' TYPE (vv "X") NAT BOOL --> if'' TYPE (vv "X") NAT BOOL))
>                        (ll "X" (ll "y" (vv "y")))
>                    (_PI "X" BOOL (if'' TYPE (vv "X") NAT BOOL --> if'' TYPE (vv "X") NAT BOOL))
>                        (ll "X" (mv "A" $$ vv "X"))
>           ]

>           -- test 12: solve f with \ _ y . y after lifting type
>         , ( gal "f" (_PI "Y" BOOL (if'' TYPE (vv "Y") NAT BOOL --> if'' TYPE (vv "Y") NAT BOOL))
>           : boy "X" BOOL
>             ( eq "p" (if'' TYPE (vv "X") NAT BOOL --> if'' TYPE (vv "X") NAT BOOL) (ll "y" (vv "y"))
>                      (if'' TYPE (vv "X") NAT BOOL --> if'' TYPE (vv "X") NAT BOOL) (mv "f" $$ vv "X")
>             : [])
>           )

>           -- test 13: intersection with nonlinearity, restrict F to first two args
>         , ( gal "F" (BOOL --> BOOL --> BOOL --> BOOL) 
>           : boy "X" BOOL
>             ( boy "Y" BOOL
>               ( eq "p" BOOL (mv "F" $$$ [vv "X", vv "X", vv "Y"])
>                        BOOL (mv "F" $$$ [vv "X", vv "X", vv "X"])
>               : [])
>             )
>           )

>           -- test 14: heterogeneous equality
>         , [ gal "A" TYPE
>           , gal "B" TYPE
>           , eq "q" TYPE (mv "A") TYPE (mv "B")
>           , eq "p" (mv "A" --> BOOL) (ll "a" TRUE)
>                    (mv "B" --> BOOL) (ll "b" TRUE)
>           ]

>           -- test 15: sigma metavariable; solve A with ((?, TRUE), ?)
>         , [ gal "A" (_SIG "X" (NAT *: BOOL) (if'' TYPE (vv "X" %% Tl) NAT BOOL))
>           , eq "p" BOOL TRUE BOOL (mv "A" %% Hd %% Tl)
>           ]

>           -- test 16: sigma variable; solve A with \ X Y . X &&& Y
>         , ( gal "A" (BOOL --> BOOL --> BOOL)
>           : boy "B" (_SIG "X" BOOL (if'' TYPE (vv "X") NAT BOOL *: BOOL))
>             ( eq "p" BOOL (mv "A" $$ (vv "B" %% Hd) $$ (vv "B" %% Tl %% Tl))
>                      BOOL ((vv "B" %% Hd) &&& (vv "B" %% Tl %% Tl))
>             : [])
>           )

>           -- test 17: sigma variable; restrict A to \ _ X . ?A' X
>         , ( gal "A" (BOOL --> BOOL --> BOOL)
>           : boy "B" (_SIG "X" BOOL (if'' TYPE (vv "X") NAT BOOL *: BOOL))
>             ( eq "p" BOOL (mv "A" $$$ [vv "B" %% Hd, vv "B" %% Tl %% Tl])
>                      BOOL (mv "A" $$$ [vv "B" %% Tl %% Tl, vv "B" %% Tl %% Tl])
>             : [])
>           )

>           -- test 18: sigma variable; solve B with \ X z . ?A X (z -)
>         , ( gal "A" (BOOL --> BOOL --> BOOL)
>           : gal "B" (_PI "X" BOOL (NAT *: BOOL --> BOOL))
>           : boy "C" (_SIG "X" BOOL (NAT *: BOOL))
>             ( eq "p" BOOL (mv "A" $$$ [vv "C" %% Hd, vv "C" %% Tl %% Tl])
>                      BOOL (mv "B" $$$ [vv "C" %% Hd, vv "C" %% Tl])
>             : [])
>           )

>           -- test 19: sigma metavariable and equation; solve A
>         , [ gal "A" (_SIG "X" BOOL (if'' TYPE (vv "X") NAT BOOL))
>           , eq "p" (_SIG "X" BOOL (if'' TYPE (vv "X") NAT BOOL *: BOOL))
>                        (PAIR (mv "A" %% Hd) (PAIR (mv "A" %% Tl) TRUE))
>                    (_SIG "X" BOOL (if'' TYPE (vv "X") NAT BOOL *: BOOL))
>                        (PAIR TRUE (PAIR (SU ZE) (mv "A" %% Hd)))
>           ]

>           -- test 20: solve A with X ! and a with X -
>         , ( boy "X" (_SIG "Y" BOOL (if'' TYPE (vv "Y") NAT BOOL))
>             ( gal "A" BOOL
>             : gal "a" (if'' TYPE (mv "A") NAT BOOL)
>             : eq "p" (_SIG "Y" BOOL (if'' TYPE (vv "Y") NAT BOOL)) (vv "X")
>                      (_SIG "Y" BOOL (if'' TYPE (vv "Y") NAT BOOL)) (PAIR (mv "A") (mv "a"))
>             : [])
>           )

>           -- test 21: solve A with f
>         , ( boy "f" (BOOL --> BOOL)
>             ( gal "A" (BOOL --> BOOL)
>             : eq "p" (BOOL --> BOOL) (vv "f")
>                      (BOOL --> BOOL) (ll "x" (mv "A" $$ vv "x"))
>             : [])
>           )

>           -- test 22: solve A with TRUE
>         , ( boy "X" ((BOOL --> BOOL) *: BOOL)
>             ( gal "A" BOOL
>             : eq "p" BOOL (vv "X" %% Hd $$ TRUE) BOOL (vv "X" %% Hd $$ mv "A")
>             : [])
>           )

>           -- test 23: solve SS with [S', S']
>         , ( gal "SS" (BOOL *: BOOL)
>           : boy "f" (BOOL --> BOOL --> BOOL)
>             ( eq "p" BOOL (vv "f" $$$ [mv "SS" %% Tl, mv "SS" %% Hd])
>                      BOOL (vv "f" $$$ [mv "SS" %% Hd, mv "SS" %% Tl])
>             : [])
>           )

>           -- test 24: solve A with TRUE
>         , [ gal "A" BOOL
>           , eq "q" TYPE (if'' TYPE (mv "A") NAT BOOL) TYPE NAT
>           , eq "p" (if'' TYPE (mv "A") NAT BOOL --> BOOL) (ll "a" (mv "A"))
>                    (NAT --> BOOL) (ll "a" TRUE)
>           ]

>           -- test 25: fill a gap
>         , ( eq "p" TYPE (BOOL --> BOOL) TYPE (BOOL --> BOOL)
>           : [])

>           -- test 26: solve A with \ _ Y . Y
>         , ( gal "A" (BOOL --> BOOL --> BOOL)
>           : boy "X" BOOL
>             ( boy "Z" BOOL      
>               ( eq "p" (if'' TYPE (mv "A" $$ vv "X" $$ vv "X") BOOL NAT --> BOOL)
>                            (ll "Y" (mv "A" $$ vv "X" $$ vv "Z"))
>                        (if'' TYPE (vv "X") BOOL NAT --> BOOL)
>                            (ll "Y" (vv "X"))
>               : [])
>             )
>           )

>           -- test 27: solve A with TRUE
>         , [ gal "A" BOOL
>           , eq "p" ((BOOL --> BOOL) --> BOOL) (ll "X" (vv "X" $$ mv "A"))
>                    ((BOOL --> BOOL) --> BOOL) (ll "X" (vv "X" $$ TRUE))
>           ]

>           -- test 28: prune and solve A with \ _ . B -> B
>         , ( gal "A" (BOOL --> BOOL)
>           : gal "B" (BOOL --> BOOL)
>           : boy "x" (BOOL *: BOOL)  
>             ( eq "p" BOOL (mv "A" $$ (vv "x" %% Hd))
>                      BOOL (mv "B" $$ TRUE)
>             : [])
>           )

>           -- test 29: prune A and solve B with A
>         , ( gal "A" (BOOL --> BOOL)
>           : gal "B" BOOL
>           : eq "p" (BOOL --> BOOL) (ll "X" (mv "A" $$ (vv "X" &&& vv "X")))
>                    (BOOL --> BOOL) (ll "X" (mv "B"))
>           : [])

>           -- test 30: prune A and solve B with A
>         , ( gal "B" BOOL
>           : gal "A" (BOOL --> BOOL)
>           : eq "p" (BOOL --> BOOL) (ll "X" (mv "A" $$ (vv "X" &&& vv "X")))
>                    (BOOL --> BOOL) (ll "X" (mv "B"))
>           : [])

>           -- test 31: solve A with BOOL and f with \ x . x
>         , ( gal "A" TYPE
>           : gal "f" (mv "A" --> BOOL)
>           : eq "p" (mv "A" --> BOOL) (mv "f")
>                    (mv "A" --> mv "A") (ll "x" (vv "x"))
>           : eq "q" TYPE (mv "A" --> BOOL) TYPE (mv "A" --> mv "A")
>           : [])

>           -- test 32: prune B and solve A with f B B 
>         , ( boy "f" (BOOL --> BOOL --> BOOL)
>             ( gal "A" BOOL
>             : gal "B" (BOOL --> BOOL)
>             : eq "p" (BOOL --> BOOL) (ll "Y" (mv "A"))
>                      (BOOL --> BOOL) (ll "X" (vv "f" $$ (mv "B" $$ vv "X")
>                                                      $$ (mv "B" $$ mv "A")))
>             : [])
>           )

>           -- test 33: eta-contract pi
>         , ( gal "A" ((BOOL --> BOOL) --> BOOL)
>           : boy "f" (BOOL --> BOOL)
>             ( eq "p" BOOL (mv "A" $$ (ll "y" (vv "f" $$ vv "y")))
>                      BOOL (vv "f" $$ TRUE)
>             : [])
>           )

>           -- test 34: eta-contract sigma
>         , ( gal "A" (BOOL *: BOOL --> BOOL)
>           : boy "b" (BOOL *: BOOL)
>             ( eq "p" BOOL (mv "A" $$ (PAIR (vv "b" %% Hd) (vv "b" %% Tl)))
>                      BOOL (vv "b" %% Hd)
>             : [])
>           )

>           -- test 35: eta-contract pi and sigma
>         , ( gal "A" ((BOOL *: BOOL --> BOOL) --> BOOL)
>           : boy "f" (BOOL *: BOOL --> BOOL)
>             ( eq "p" BOOL (mv "A" $$ (ll "b" (vv "f" $$ PAIR (vv "b" %% Hd) (vv "b" %% Tl))))
>                      BOOL (vv "f" $$ PAIR TRUE FALSE)
>             : [])
>           )

>           -- test 36: A/P Flattening Sigma-types
>         , ( gal "u" ((BOOL --> BOOL *: BOOL) --> BOOL)
>           : boy "z1" (BOOL --> BOOL)
>             ( boy "z2" (BOOL --> BOOL)
>               ( eq "p" BOOL (mv "u" $$ (ll "x" (PAIR (vv "z1" $$ vv "x") (vv "z2" $$ vv "x"))))
>                        BOOL TRUE
>               : [])
>             )
>           )

>           -- test 37: A/P Eliminating projections
>         , ( gal "u" ((BOOL --> BOOL) --> BOOL)
>           : boy "y" (BOOL --> BOOL *: BOOL)
>             ( eq "p" BOOL (mv "u" $$ (ll "x" (vv "y" $$ vv "x" %% Hd)))
>                      BOOL (vv "y" $$ TRUE %% Hd)
>             : [])
>           )

>           -- test 38: prune A and solve B with A
>         , ( gal "B" BOOL
>           : gal "A" (BOOL --> BOOL)
>           : eq "p" (BOOL --> BOOL) (ll "X" (mv "B"))
>                    (BOOL --> BOOL) (ll "X" (mv "A" $$ (vv "X" &&& vv "X")))
>                    
>           : [])

>           -- test 39: solve u with \ _ x . x
>         , ( gal "u" (_PI "v" (_SIG "S" BOOL (if'' TYPE (vv "S") BOOL NAT *: (if'' TYPE (vv "S") BOOL NAT --> BOOL)))
>                         (if'' TYPE (vv "v" %% Tl %% Tl $$ (vv "v" %% Tl %% Hd)) BOOL NAT --> if'' TYPE (vv "v" %% Tl %% Tl $$ (vv "v" %% Tl %% Hd)) BOOL NAT))
>           : boy "A" BOOL
>             ( boy "a" (if'' TYPE (vv "A") BOOL NAT)
>               ( boy "f" (if'' TYPE (vv "A") BOOL NAT --> BOOL)
>                 ( eq "p" (if'' TYPE (vv "f" $$ vv "a") BOOL NAT --> if'' TYPE (vv "f" $$ vv "a") BOOL NAT)
>                              (mv "u" $$ PAIR (vv "A") (PAIR (vv "a") (vv "f")))
>                          (if'' TYPE (vv "f" $$ vv "a") BOOL NAT --> if'' TYPE (vv "f" $$ vv "a") BOOL NAT)
>                              (ll "x" (vv "x"))
>                 : [])
>               )
>             )
>           )

>           -- test 40: restrict A to second argument
>         , ( gal "A" (BOOL --> BOOL --> BOOL)
>           : boy "X" BOOL
>             ( boy "Y" BOOL
>               ( eq "p" (BOOL --> BOOL) (mv "A" $$ vv "X")
>                        (BOOL --> BOOL) (ll "Z" (mv "A" $$ vv "Y" $$ vv "Z"))
>               : [])
>             )
>           )

>           -- test 41: solve A with [ TRUE , TRUE ]
>         , ( gal "A" (BOOL *: BOOL)
>           : eq "p" (BOOL *: BOOL) (mv "A")
>                    (BOOL *: BOOL) (PAIR (mv "A" %% Tl) TRUE)
>           : [])

>           -- test 42
>         , ( gal "T" (BOOL --> BOOL)
>           : gal "A" (_PI "Y" BOOL (if'' TYPE (mv "T" $$ vv "Y") BOOL NAT --> BOOL))
>           : gal "B" BOOL
>           : boy "X" BOOL
>             ( boy "t" (if'' TYPE (mv "T" $$ vv "X") BOOL NAT)
>               ( eq "p" BOOL (mv "B") BOOL (mv "A" $$ vv "X" $$ vv "t")
>               : [])
>             )
>           )

>           -- test 43
>         , ( gal "A" (BOOL --> BOOL)
>           : gal "F" (BOOL --> BOOL)
>           : gal "B" BOOL
>           : boy "X" BOOL
>             ( eq "p" (BOOL *: BOOL) (PAIR (mv "B") (mv "B"))
>                      (BOOL *: BOOL) (PAIR (mv "A" $$ (mv "F" $$ vv "X")) (mv "A" $$ vv "X"))
>             : [])
>           )

>           -- test 44: false occurrence
>         , ( gal "A" BOOL
>           : gal "B" BOOL
>           : gal "C" TYPE
>           : eq "p" (mv "C" --> BOOL) (lamK (mv "B"))
>                    (mv "C" --> BOOL) (lamK (mv "A"))
>           : [])

>           -- test 45
>         , ( gal "A" TYPE
>           : gal "B" (mv "A" --> BOOL)
>           : gal "C" (mv "A" --> BOOL)
>           : boy "x" (mv "A")
>             ( boy "y" (mv "A")
>               ( eq "p" BOOL (mv "B" $$ vv "x")
>                        BOOL (mv "C" $$ vv "x")
>               : [])
>             )
>           )

>           -- test 46: prune p to learn B doesn't depend on its argument
>         , ( gal "A" (BOOL --> BOOL)
>           : boy "Z" BOOL
>             ( gal "B" (BOOL --> BOOL)
>             : gal "C" BOOL
>             : boy "X" BOOL
>               ( boy "Y" BOOL
>                 ( eq "p" BOOL (mv "A" $$ (mv "B" $$ mv "C"))
>                          BOOL (mv "B" $$ vv "Y")
>                 : eq "q" BOOL (mv "B" $$ mv "C") BOOL (vv "Z")
>                 : [])
>               )
>             )
>           )

>           -- test 47
>         , ( gal "A" (_PI "X" BOOL (BOOL --> BOOL))
>           : gal "B" BOOL
>           : boy "Y" BOOL
>             ( boy "y" BOOL
>               ( eq "p" BOOL (mv "B")
>                        BOOL (mv "A" $$ vv "Y" $$ vv "y")
>               : [])
>             )
>           )

>           -- test 48
>         , ( gal "A" (BOOL --> BOOL)
>           : gal "B" TYPE
>           : eq "p" TYPE (mv "B")
>                    TYPE (_PI "X" BOOL (if'' TYPE (mv "A" $$ vv "X") BOOL BOOL))
>                    
>           : [])

>           -- test 49: don't prune A too much
>         , ( gal "F" (BOOL --> BOOL --> BOOL)
>           : gal "A" (_PI "X" BOOL (if'' TYPE (mv "F" $$ TRUE $$ vv "X") BOOL NAT --> BOOL))
>           : gal "B" (BOOL --> BOOL)
>           : boy "Y" BOOL
>             ( eq "p" (BOOL --> BOOL) (mv "B")
>                      (if'' TYPE (mv "F" $$ TRUE $$ vv "Y") BOOL NAT --> BOOL) (mv "A" $$ vv "Y")
>             : boy "y" (if'' TYPE (mv "F" $$ TRUE $$ vv "Y") BOOL NAT)
>               ( eq "q" BOOL (mv "F" $$ vv "Y" $$ vv "Y") BOOL TRUE
>               : eq "r" BOOL (mv "A" $$ vv "Y" $$ vv "y")
>                        (if'' TYPE (mv "F" $$ TRUE $$ vv "Y") BOOL NAT) (vv "y")
>               : [])
>             )
>           )

>           -- test 50: Miller's nasty non-pruning example
>         , ( boy "a" BOOL
>             ( gal "X" ((BOOL --> BOOL) --> BOOL --> BOOL)
>             : boy "y" BOOL
>               ( eq "p" BOOL (mv "X" $$ (ll "z" (vv "a")) $$ vv "y")
>                        BOOL (vv "a")
>               : eq "q" ((BOOL --> BOOL) --> BOOL --> BOOL) (mv "X")
>                        ((BOOL --> BOOL) --> BOOL --> BOOL) (ll "z1" (ll "z2" (vv "z1" $$ vv "z2")))
>               : [])
>             )
>           )

>           -- test 51
>         , ( gal "A" (_PI "X" BOOL (_PI "x" BOOL BOOL))
>           : gal "B" TYPE
>           : eq "p" TYPE (mv "B")
>                    TYPE (_PI "X" BOOL (_PI "x" BOOL (if'' TYPE (mv "A" $$ vv "X" $$ vv "x") BOOL BOOL)))
>           : [])

>           -- test 52
>         , ( gal "b" BOOL
>           : eq "p" BOOL (mv "b") BOOL TRUE
>           : [])

>           -- test 53
>         , ( gal "b" BOOL
>           : gal "X" (if'' TYPE (mv "b") BOOL (BOOL --> BOOL))
>           : eq "p" (BOOL --> BOOL) (ll "Y" (vv "Y"))
>                    (if'' TYPE (mv "b") BOOL (BOOL --> BOOL)) (mv "X")
>           : eq "q" BOOL (mv "b") BOOL FALSE
>           : [])

>           -- test 54: twins with matching spines
>         , ( gal "A" TYPE
>           : gal "B" (BOOL --> mv "A" --> BOOL)
>           : gal "S" TYPE
>           : gal "T" (BOOL --> mv "S" --> BOOL)
>           : eq "p" (_SIG "x" (mv "A") BOOL --> mv "A")
>                         (ll "x" (vv "x" %% Hd))
>                     (_SIG "x" (mv "S") BOOL --> mv "S")
>                         (ll "x" (vv "x" %% Hd))
>           : eq "q" TYPE (mv "A") TYPE (mv "S")
>           : [])

>           -- test 55
>         , ( gal "a" BOOL
>           : gal "b" (if'' TYPE (mv "a") BOOL BOOL)
>           : gal "c" (if'' TYPE (mv "a") BOOL BOOL)
>           : eq "p" (if'' TYPE (mv "a") BOOL BOOL) (mv "b")
>                    (if'' TYPE (mv "a") BOOL BOOL) (mv "c")
>           : [])

>           -- test 56: double meta
>         , [ gal "A" (BOOL --> BOOL)
>           , gal "B" (BOOL --> BOOL)
>           , gal "D" BOOL
>           , gal "C" BOOL
>           , eq "p" BOOL (mv "A" $$ (mv "B" $$ mv "C")) BOOL (mv "D")
>           ]

>           -- test 57: rigid-rigid mismatch disappears after eta (good order)
>         , ( gal "a" BOOL
>           : eq "q" TYPE (if'' TYPE (mv "a") (BOOL *: BOOL) (BOOL *: BOOL)) TYPE (BOOL *: BOOL)
>           : boy "X" (if'' TYPE (mv "a") (BOOL *: BOOL) (BOOL *: BOOL))
>             ( gal "b" BOOL
>             : gal "c" BOOL
>             : eq "r" BOOL (mv "a") BOOL TRUE
>             : eq "p" (if'' TYPE (mv "a") (BOOL *: BOOL) (BOOL *: BOOL)) (vv "X") (BOOL *: BOOL) (PAIR (mv "b") (mv "c"))
>             : [])
>           )

>           -- test 58: rigid-rigid mismatch disappears after eta (bad order)
>         , ( gal "a" BOOL
>           : eq "q" TYPE (if'' TYPE (mv "a") (BOOL *: BOOL) (BOOL *: BOOL)) TYPE (BOOL *: BOOL)
>           : boy "X" (if'' TYPE (mv "a") (BOOL *: BOOL) (BOOL *: BOOL))
>             ( gal "b" BOOL
>             : gal "c" BOOL
>             : eq "p" (if'' TYPE (mv "a") (BOOL *: BOOL) (BOOL *: BOOL)) (vv "X") (BOOL *: BOOL) (PAIR (mv "b") (mv "c"))
>             : eq "r" BOOL (mv "a") BOOL TRUE
>             : [])
>           )

>         ]


> stucks = [ 

>           -- stuck 0: nonlinear
>           ( gal "A" (BOOL --> BOOL --> BOOL --> BOOL)
>           : gal "B" (BOOL --> BOOL)
>           : boy "X" BOOL
>             ( boy "Y" BOOL
>               ( eq "p" BOOL (mv "A" $$$ [vv "Y", vv "X", vv "Y"])
>                        BOOL (mv "B" $$ vv "Y" &&& vv "X")
>               : [])
>             )
>           )

>           -- test: dingo
>         , [ gal "X" (_PI "N" NAT (fold'' TYPE BOOL "IH" (vv "IH") (vv "N") --> BOOL)) 
>           , eq "p" BOOL (mv "X" $$$ [ZE, FALSE])
>                    BOOL (mv "X" $$$ [ZE, TRUE])
>           ]

>           -- test: dingo
>         , [ gal "X" (_PI "N" NAT (fold'' TYPE BOOL "IH" (vv "IH") (vv "N") --> BOOL)) 
>           , eq "p" BOOL (mv "X" $$$ [ZE, FALSE])
>                    BOOL (mv "X" $$$ [SU ZE, FALSE])
>           ]

>           -- stuck 1: nonlinear
>         , ( gal "F" (BOOL --> BOOL --> BOOL) 
>           : gal "G" (BOOL --> BOOL --> BOOL)
>           : boy "X" BOOL
>             ( eq "p" BOOL (mv "F" $$$ [vv "X", vv "X"])
>                      BOOL (mv "G" $$$ [vv "X", vv "X"])
>             : [])
>           )

>           -- stuck 2: nonlinear
>         , ( gal "f" (BOOL --> BOOL --> BOOL)
>           : boy "x" BOOL
>                 ( eq "p" (BOOL --> BOOL) (ll "y" (mv "f" $$ vv "x" $$ vv "x"))
>                          (BOOL --> BOOL) (ll "y" (vv "x"))
>                 : [])
>            )

>           -- stuck 3: nonlinear
>         , ( gal "B" (BOOL --> BOOL --> BOOL)
>           : gal "A" TYPE
>           : boy "X" BOOL
>             ( eq "p" (mv "A" --> BOOL) (ll "a" (mv "B" $$ vv "X" $$ vv "X"))
>                      (mv "A" --> BOOL) (ll "a" (vv "X"))
>             : [])
>           )

>           -- stuck 4: solution does not typecheck 
>         , ( gal "A" TYPE
>           : gal "f" (mv "A" --> BOOL)
>           : eq "p" (mv "A" --> BOOL) (mv "f")
>                    (mv "A" --> mv "A") (ll "x" (vv "x"))
>           : [])

>           -- stuck 5: weak rigid occurrence should not cause failure
>         , ( gal "A" ((NAT --> NAT) --> NAT)
>           : boy "f" (NAT --> NAT)
>             ( eq "p" NAT (mv "A" $$ vv "f")
>                      NAT (SU (vv "f" $$ (mv "A" $$ (ll "X" (vv "X")))))
>             : [])
>           )

>           -- stuck 6: cannot safely prune second argument of B
>         , ( gal "A" BOOL
>           : gal "B" (BOOL --> BOOL --> BOOL)
>           : boy "X" BOOL
>             ( eq "p" BOOL (mv "A")
>                      BOOL (mv "B" $$ mv "A" $$ vv "X")
>             : [])
>           )

>           -- stuck 7 (requires sigma-splitting of twins)
>         , ( gal "A" TYPE
>           : gal "B" (BOOL --> mv "A" --> BOOL)
>           : gal "S" TYPE
>           : gal "T" (BOOL --> mv "S" --> BOOL)
>           : eq "p" (_SIG "x" (mv "A") BOOL --> BOOL)
>                         (ll "x" (mv "B" $$ TRUE $$ (vv "x" %% Hd)))
>                     (_SIG "x" (mv "S") BOOL --> BOOL)
>                         (ll "x" (mv "T" $$ TRUE $$ (vv "x" %% Hd)))
>           : [])

>           -- stuck 8: awkward occurrence
>         , ( gal "A" TYPE
>           : gal "a" (mv "A")
>           : gal "f" (mv "A" --> BOOL)
>           : eq "p" TYPE (mv "A") TYPE (if'' TYPE (mv "f" $$ mv "a") NAT BOOL --> BOOL)
>           : [])

>           -- stuck 9
>         , ( gal "A" (BOOL --> BOOL)
>           : gal "B" (BOOL --> BOOL)
>           : gal "a" (if'' TYPE (mv "A" $$ TRUE) NAT BOOL)
>           : gal "b" (if'' TYPE (mv "B" $$ TRUE) NAT BOOL)
>           : eq "p" (_SIG "x" BOOL (if'' TYPE (mv "B" $$ vv "x") NAT BOOL))
>                        (PAIR TRUE (mv "b"))
>                    (if'' TYPE (mv "A" $$ TRUE) NAT BOOL)
>                        (mv "a")
>           : eq "q" TYPE (_SIG "x" BOOL (if'' TYPE (mv "B" $$ vv "x") NAT BOOL))
>                    TYPE (if'' TYPE (mv "A" $$ TRUE) NAT BOOL)
>           : [])

>           -- stuck 10
>         , ( gal "A" (BOOL --> BOOL)
>           : gal "B" BOOL
>           : boy "X" BOOL
>             ( eq "p" BOOL (mv "A" $$ (mv "A" $$ vv "X"))
>                      BOOL (mv "B")
>             : [])
>           )

>           -- stuck 11
>         , ( gal "F" (BOOL --> BOOL)
>           : gal "A" (_PI "X" BOOL (if'' TYPE (mv "F" $$ vv "X") BOOL BOOL))
>           : boy "X" BOOL
>             ( boy "Y" BOOL
>               ( eq "p" (if'' TYPE (mv "F" $$ vv "X") BOOL BOOL) (mv "A" $$ vv "X")
>                        (if'' TYPE (mv "F" $$ vv "Y") BOOL BOOL) (mv "A" $$ vv "Y")
>               : [])
>             )
>           )

>           -- stuck 12
>         , ( gal "B" (BOOL --> BOOL)
>           : gal "F" (if'' TYPE (mv "B" $$ TRUE) BOOL BOOL --> BOOL)
>           : eq "p" (if'' TYPE (mv "B" $$ TRUE) BOOL BOOL --> BOOL)
>                        (ll "Y" (mv "F" $$ vv "Y"))
>                    (BOOL --> BOOL) 
>                        (ll "Y" (vv "Y"))
>           : [])

>           -- test 54: solve C with A despite B being in the way
>         , ( gal "A" BOOL
>           : gal "C" BOOL
>           : gal "B" (BOOL --> BOOL)
>           : gal "F" (if'' TYPE (mv "B" $$ TRUE) BOOL BOOL --> BOOL)
>           : eq "p" (_PI "X" (if'' TYPE (mv "B" $$ TRUE) BOOL BOOL) (if'' TYPE (mv "F" $$ vv "X") BOOL BOOL --> BOOL))
>                        (ll "X" (ll "x" (mv "A")))
>                    (_PI "X" BOOL (if'' TYPE (vv "X") BOOL BOOL --> BOOL))
>                        (ll "X" (ll "x" (mv "C")))
>           : eq "q" TYPE (_PI "X" (if'' TYPE (mv "B" $$ TRUE) BOOL BOOL) (if'' TYPE (mv "F" $$ vv "X") BOOL BOOL --> BOOL)) TYPE (_PI "X" BOOL (if'' TYPE (vv "X") BOOL BOOL --> BOOL))
>           : [])

>           -- test 25: solve with extensionality and refl
>         , [ gal "A" BOOL
>           , eq "p" (if'' TYPE (mv "A") NAT BOOL --> BOOL) (ll "x" TRUE)
>                    (NAT --> BOOL) (ll "x" TRUE)
>           , eq "q" TYPE (if'' TYPE (mv "A") NAT BOOL) TYPE NAT
>           ]

>         ]

> fails = [ 

-- >           tests !! 0 ,

>           -- fail 0: occur check failure (A occurs in suc A)
>           [ gal "A" NAT
>           , eq "p" NAT (mv "A") NAT (SU (mv "A"))
>           ]

>           -- fail 1: flex-rigid fails because A cannot depend on X
>         , ( gal "A" BOOL
>           : gal "B" BOOL
>           : boy "X" BOOL
>             ( eq "p" BOOL (mv "A") BOOL (vv "X" &&& mv "B")
>             : [])
>           )

>           -- fail 2: rigid-rigid clash
>         , ( boy "X" BOOL
>             ( boy "Y" BOOL
>               ( eq "p" BOOL (vv "X") BOOL (vv "Y")
>               : [])
>             )
>           )

>           -- fail 3: spine mismatch
>         , ( boy "X" (BOOL *: BOOL)
>             ( eq "p" BOOL (vv "X" %% Hd) BOOL (vv "X" %% Tl)
>             : [])
>           )

>           -- fail 4: rigid-rigid constant clash
>         , ( eq "p" BOOL TRUE BOOL FALSE
>           : [])

>           -- fail 5: spine mismatch
>         , ( eq "p" (BOOL --> BOOL) (ll "x" (vv "x"))
>                    ((BOOL --> BOOL) --> BOOL) (ll "f" (vv "f" $$ TRUE))
>           : [])

>           -- fail 6
>         , ( eq "p" TYPE BOOL TYPE (BOOL --> BOOL)
>           : [])

>           -- fail 7
>         , ( gal "A" TYPE
>           : boy "x" (mv "A")
>             ( boy "y" (mv "A")
>               ( eq "p" (mv "A") (vv "x") (mv "A") (vv "y")
>               : [])
>             )
>           )

>           -- fail 8
>         , ( gal "A" TYPE
>           : boy "x" (mv "A")
>             ( eq "p" (mv "A") (vv "x") BOOL TRUE
>             : [])
>           )

>           -- fail 9: occur check
>         , ( boy "f" (BOOL --> BOOL)
>             ( gal "A" (BOOL --> BOOL)
>             : boy "X" BOOL
>               ( boy "Y" BOOL
>                 ( eq "p" BOOL (mv "A" $$ vv "X")
>                          BOOL (vv "f" $$ (mv "A" $$ vv "Y"))
>                 : [])
>               )
>             )
>           )


>         ]

> main = patternUnify
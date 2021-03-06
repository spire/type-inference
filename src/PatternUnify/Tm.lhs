%if False

> {-# OPTIONS_GHC -F -pgmF she #-}
> {-# LANGUAGE GADTs, KindSignatures, TemplateHaskell,
>       FlexibleInstances, MultiParamTypeClasses, FlexibleContexts,
>       UndecidableInstances, TypeSynonymInstances, ScopedTypeVariables,
>       DeriveFunctor, DeriveFoldable, StandaloneDeriving, PatternGuards,
>       DeriveTraversable, TupleSections #-}

> module PatternUnify.Tm where

> import Prelude hiding (foldl, foldr, elem)
> import Control.Applicative (Applicative, pure, (<*>), (<$>))
> import Control.Monad.Reader (MonadReader, local)
> import Data.Foldable (Foldable, foldlM, foldr, toList)
> import Data.Function (on)
> import Data.List (unionBy)
> import Data.Monoid hiding ((<>))
> import Data.Traversable (Traversable, traverse)
> import qualified Data.Set as Set
> import Data.Set (Set, member)

> import Common.Names
> import Common.PrettyPrint
> import Common.BwdFwd

%endif

First I define terms and machinery for working with them (including
evaluation and occurrence checking), based on the description in
Subsection~\longref{subsec:miller:terms}.

Object language terms are represented using the data type |Tm|.  The
Binders Unbound library of \citet{weirich2011:binders-unbound} defines
the |Bind| type constructor and gives a cheap locally nameless
representation with operations including $\alpha$-equivalence and
substitution for first-order datatypes containing terms.  I use a
single constructor for all the canonical forms (that do not involve
binding) so as to factor out common patterns in the typechecker.

> data Tm where
>     L        :: Bind Nom Tm -> Tm
>     N        :: Head -> Bwd Elim -> Tm
>     C        :: Can Tm -> Tm
>     Pi, Sig  :: Type -> Bind Nom Type -> Tm

> type Nom    = Name Tm
> data Can t  = Type
>             | Pair t t
>             | Bool | True' | False'
>             | Nat | Ze | Su t
>             | Unit | Tt
>   deriving (Traversable)
> data Head   = V Nom Twin | M Nom
> data Twin   = Only | TwinL | TwinR
> data Elim   = A Tm
>             | Hd | Tl
>             | If (Bind Nom Type) Tm Tm
>             | Fold (Bind Nom Type) Tm (Bind Nom (Bind Nom Tm))
>             -- No trivial unit eliminator: we don't have one in Spire.
>
> type Type   = Tm


The non-binding canonical forms |Can| induce a |Foldable| functor
(which can be derived automatically by GHC).  Annoyingly, |Elim|
cannot be made a functor in the same way, because |Bind Nom| is not a
functor on |*| but only on the subcategory induced by |Alpha|.
However, the action on morphisms can be defined thus:

> mapElim :: (Fresh m , Applicative m) => (Tm -> m Tm) -> Elim -> m Elim
> mapElim f  (A a)        = A <$> f a
> mapElim _  Hd           = return Hd
> mapElim _  Tl           = return Tl
> mapElim f  (If _P ct cf)  = do
>   (x , _P') <- unbind _P
>   If <$> (bind x <$> f _P') <*> f ct <*> f cf
> mapElim f  (Fold _P cz cs)  = do
>   (x , _P') <- unbind _P
>   (y , cs') <- unbind cs
>   (z , cs'') <- unbind cs'
>   Fold <$> (bind x <$> f _P') <*> f cz <*> (bind y . bind z <$> f cs'')
>
> foldMapElim :: (Monoid mon , Fresh m , Applicative m) => (Tm -> m mon) -> Elim -> m mon
> foldMapElim f  (A a)        = f a
> foldMapElim _  Hd           = return $ mempty
> foldMapElim _  Tl           = return $ mempty
> foldMapElim f  (If _T s t)  = do
>   (_ , _T') <- unbind _T
>   mconcat <$> mapM f [ _T' , s , t ]
> foldMapElim f  (Fold _P cz cs) = do
>   (_ , _P') <- unbind _P
>   (_ , cs'') <- unbind =<< (snd <$> unbind cs)
>   mconcat <$> mapM f [ _P' , cz , cs'' ]


%if False

> deriving instance Show Tm
> deriving instance Eq t => Eq (Can t)
> deriving instance Show t => Show (Can t)
> deriving instance Functor Can
> deriving instance Foldable Can
> deriving instance Eq Twin
> deriving instance Show Twin
> deriving instance Eq Head
> deriving instance Show Head
> deriving instance Show Elim

> instance Eq Elim where
>   (==) = aeq

> instance Eq Tm where
>     (==) = aeq

> instance Alpha Tm
> instance Alpha t => Alpha (Can t)
> instance Alpha Twin
> instance Alpha Head
> instance Alpha Elim

Substitution.

> instance (Fresh m , Applicative m) => SubstM m Tm Tm where
>   substsM = eval
>   substM n u = substsM [(n, u)]

> instance SubstM m Tm t => SubstM m Tm (Can t)
> instance SubstM m Tm t => SubstM m Tm (Bwd t)
> instance Monad m => SubstM m Tm Twin
> instance Monad m => SubstM m Tm Head
> instance (Fresh m , Applicative m) => SubstM m Tm Elim

> instance Pretty Tm where
>     pretty (Pi _S b) =
>       lunbind b $ \ (x, _T) ->
>       wrapDoc PiSize $
>       if x <? _T
>       then (\ x' _S' _T' -> text "Pi" <+> parens (x' <+> colon <+> _S') <+> _T')
>            <$> prettyHigh x <*> prettyHigh _S <*> prettyAt ArgSize _T
>       else between (text "->") <$> prettyAt AppSize _S <*> prettyAt PiSize _T
>
>     pretty (Sig _S b) =
>       lunbind b $ \ (x, _T) ->
>       wrapDoc PiSize $
>       if x <? _T
>       then (\ x' _S' _T' -> text "Sig" <+> parens (x' <+> colon <+> _S') <+> _T')
>            <$> prettyHigh x <*> prettyHigh _S <*> prettyAt ArgSize _T
>       else between (text "*") <$> prettyAt AppSize _S <*> prettyAt PiSize _T
>     pretty (L b) = wrapDoc LamSize $ (text "\\" <+>) <$> prettyLam b
>       where
>         prettyLam u = lunbind u $ \ (x, t) -> do
>             v <- if x <? t then prettyLow x else return (text "_")
>             case t of
>                 L b'  -> (v <+>) <$> prettyLam b'
>                 _     -> (\ t' -> v <+> text "." <+> t') <$> prettyAt LamSize t
>     pretty (N h B0) = pretty h
>     pretty (N h as) = prettyElim (pretty h) (fwd as)
>     pretty (C c)    = pretty c

> instance Pretty (Can Tm) where
>     pretty Type        = return $ text "Type"
>     pretty Bool        = return $ text "Bool"
>     pretty True'       = return $ text "True"
>     pretty False'      = return $ text "False"
>     pretty Unit        = return $ text "Unit"
>     pretty Tt          = return $ text "Tt"
>     pretty Nat         = return $ text "Nat"
>     pretty Ze          = prettyNat 0 ZE
>     pretty (Su n)      = prettyNat 1 n
>     pretty (Pair s t)  = wrapDoc AppSize $ do
>         s' <- prettyAt ArgSize s
>         t' <- prettyAt ArgSize t
>         return $ text "Pair" <+> s' <+> t'

> prettyNat :: (Applicative m, LFresh m, MonadReader Size m) =>
>                  Int -> Tm -> m Doc
> prettyNat n ZE      = return $ int n
> prettyNat n (SU m)  = prettyNat (succ n) m
> prettyNat n t       = do  t' <- pretty t
>                           return $ int n <+> text "+" <+> t'


> instance Pretty Twin where
>     pretty Only   = (| empty |)
>     pretty TwinL  = (| (text "^<") |)
>     pretty TwinR  = (| (text "^>") |)

> instance Pretty Head where
>     pretty (V x w)  = (| (pretty x) <> (pretty w) |)
>     pretty (M x)   = (text "?" <>) <$> pretty x

> instance Pretty Elim where
>     pretty (A a)  = pretty a
>     pretty Hd     = return $ text "!"
>     pretty Tl     = return $ text "-"
>     pretty (If f s t) = do
>         f' <- prettyAt ArgSize (L f)
>         s' <- prettyAt ArgSize s
>         t' <- prettyAt ArgSize t
>         return $ text "(IF)" <+> f' <+> s' <+> t'
>     pretty (Fold _P cz cs) = do
>         _P' <- prettyAt ArgSize (L _P)
>         cz' <- prettyAt ArgSize cz
>         lunbind cs $ \ (x , cs') -> do
>         cs'' <- prettyAt ArgSize (L (bind x (L cs')))
>         return $ text "(FOLD)" <+> _P' <+> cz' <+> cs''

> prettyElim :: (Applicative m, LFresh m, MonadReader Size m) =>
>                   m Doc -> [Elim] -> m Doc
> prettyElim d [] = d
> prettyElim d (A a : as) = prettyElim (wrapDoc AppSize $ (<+>) <$> (local (const AppSize) d) <*> local (const ArgSize) (pretty a)) as
> prettyElim d (Hd : as) = prettyElim (wrapDoc AppSize $ (<+> text "HD") <$> (local (const AppSize) d)) as
> prettyElim d (Tl : as) = prettyElim (wrapDoc AppSize $ (<+> text "TL") <$> (local (const AppSize) d)) as
> prettyElim d (If f s t : as) = prettyElim (do
>     f' <- prettyAt maxBound (L f)
>     d' <- local (const ArgSize) d
>     s' <- prettyAt ArgSize s
>     t' <- prettyAt ArgSize t
>     return $ text "IF_" <> parens f' <+> d' <+> s' <+> t'
>    ) as
> prettyElim d (Fold _P cz cs : as) = prettyElim (do
>     _P' <- prettyAt maxBound (L _P)
>     d' <- local (const ArgSize) d
>     cz' <- prettyAt ArgSize cz
>     lunbind cs $ \ (x , cs') -> do
>     cs'' <- prettyAt ArgSize (L (bind x (L cs')))
>     return $ text "FOLD_" <> parens _P' <+> cz' <+> cs'' <+> d'
>    ) as

%endif


Despite the single-constructor representation of canonical forms, it
is often neater to write code as if |Tm| had a data constructor for
each canonical constructor of the object language.  This is possible
thanks to pattern synonyms \citep{aitken1992} as implemented by the
Strathclyde Haskell Enhancement \citep{mcbride2010:she}.  Pattern
synonyms are abbreviations that can be used \scare{on the left} (in
patterns) as well as \scare{on the right} (in expressions).

> pattern TYPE          = C Type
> pattern PAIR s t      = C (Pair s t)
> pattern BOOL          = C Bool
> pattern TRUE          = C True'
> pattern FALSE         = C False'
> pattern NAT           = C Nat
> pattern ZE            = C Ze
> pattern SU n          = C (Su n)
> pattern UNIT          = C Unit
> pattern TT            = C Tt


%if False

> var :: Nom -> Tm
> var x = N (V x Only) B0

> twin :: Nom -> Twin -> Tm
> twin x w = N (V x w) B0

> meta :: Nom -> Tm
> meta x = N (M x) B0

> twinL :: Nom -> Tm
> twinL x = twin x TwinL

> twinR :: Nom -> Tm
> twinR x = twin x TwinR

> appV :: Nom -> Bwd Elim -> Tm
> appV x es = N (V x Only ) es

> appM :: Nom -> Bwd Elim -> Tm
> appM x es = N (M x) es

> lam :: Nom -> Tm -> Tm
> lam x t = L (bind x t)

> lams :: Foldable f => f Nom -> Tm -> Tm
> lams xs t = foldr lam t xs

> lams' :: (Functor f, Foldable f) => f (Nom, Type) -> Tm -> Tm
> lams' xs t = lams (fmap fst xs) t

> lamK :: Tm -> Tm
> lamK t = L (bindK t)

> bindK :: Tm -> Bind Nom Tm
> bindK t = bind (s2n "_x") t

> _Pi :: Nom -> Type -> Type -> Type
> _Pi x _S _T = Pi _S (bind x _T)

> _Pis :: Foldable f => f (Nom, Type) -> Type -> Type
> _Pis xs _T = foldr (uncurry _Pi) _T xs

> (-->) :: Type -> Type -> Type
> _S --> _T = _Pi (s2n "xp") _S _T
> infixr 5 -->

> _Sig :: Nom -> Type -> Type -> Type
> _Sig x _S _T = Sig _S (bind x _T)

> (*:) :: Type -> Type -> Type
> _S *: _T = _Sig (s2n "xx") _S _T

> vv :: String -> Tm
> vv x = var (s2n x)

> mv :: String -> Tm
> mv x = meta (s2n x)

> ll :: String -> Tm -> Tm
> ll x = lam (s2n x)

> _PI :: String -> Tm -> Tm -> Tm
> _PI x = _Pi (s2n x)

> _SIG :: String -> Tm -> Tm -> Tm
> _SIG x = _Sig (s2n x)

%endif


\subsubsection{Free variables}

Rather than definining functions to determine the free metavariables
and variables of terms directly, I use a typeclass to make them
available on the whole syntax.

> data Flavour = Vars | RigVars | Metas
>
> class Occurs t where
>     free   :: Flavour -> t -> Set Nom

> fvs, fvrigs, fmvs :: Occurs t => t -> Set Nom
> fvs       = free Vars
> fvrigs    = free RigVars
> fmvs      = free Metas

> instance Occurs Tm where
>     free l (L b)        = free l b
>     free l (C c)        = free l c
>     free l (Pi _S _T)   = free l _S `union` free l _T
>     free l (Sig _S _T)  = free l _S `union` free l _T
>
>     free RigVars    (N (V x _) e)    = singleton x `union` free RigVars e
>     free RigVars    (N (M _) _)      = Set.empty
>     free l          (N h e)          = free l h `union` free l e
>
> instance Occurs t => Occurs (Can t) where
>     free l (Pair s t)  = free l s `union` free l t
>     free l (Su n)      = free l n
>     free l _           = Set.empty
>
> instance Occurs Head where
>     free Vars       (M _)      = Set.empty
>     free RigVars    (M _)      = Set.empty
>     free Metas      (M alpha)  = singleton alpha
>     free Vars       (V x _)    = singleton x
>     free RigVars    (V x _)    = singleton x
>     free Metas      (V _ _)    = Set.empty
>
> instance Occurs Elim where
>    free l (A a)        = free l a
>    free l Hd           = Set.empty
>    free l Tl           = Set.empty
>    free l (If _T s t)  = free l _T `union` free l s `union` free l t
>    free l (Fold _P cz cs)  = free l _P `union` free l cz `union` free l cs


%if False

> (<?) :: Occurs t => Nom -> t -> Bool
> x <? t = x `member` (fmvs t `union` fvs t)

> instance Occurs t => Occurs [t] where
>     free l = unions . map (free l)

> instance Occurs t => Occurs (Bwd t) where
>     free l = free l . toList

> instance (Occurs s, Occurs t) => Occurs (s, t) where
>     free l (s, t) = free l s `union` free l t

> instance (Occurs s, Occurs t, Occurs u) => Occurs (s, t, u) where
>     free l (s, t, u) = unions [free l s, free l t, free l u]

> instance (Occurs s, Occurs t, Occurs u, Occurs v) => Occurs (s, t, u, v) where
>     free l (s, t, u, v) = unions [free l s, free l t, free l u, free l v]

> instance Occurs t => Occurs (Bind p t) where
>     free l (B _ t) = free l t

%endif


\subsubsection{Evaluation by hereditary substitution}

Substitutions are implemented as finite maps from names to terms; as a
technical convenience there is no distinction between substitution and
metasubstitution.

> type Subs = [(Nom, Tm)]

> (*%*) :: (Fresh m , Applicative m) => Subs -> Subs -> m Subs
> delta' *%* delta = unionBy ((==) `on` fst) delta' <$> substsM delta' delta

The evaluator is an implementation of hereditary substitution defined
in Figure~\longref{fig:miller:heresubst}: it proceeds structurally
through terms, replacing variables with their values and eliminating
redexes using the |(%%)| operator defined below.

> eval :: (Fresh m , Applicative m) => Subs -> Tm -> m Tm
> eval g (L b)        = L <$> (evalUnder g b)
> eval g (N h e)      = do
>   let h' = evalHead g h
>   e' <- mapElim (eval g) `traverse` e
>   foldlM (%%) h' e'
> eval g (C c)        = C <$> (eval g `traverse` c)
> eval g (Pi _S _T)   = Pi <$> eval g _S <*> evalUnder g _T
> eval g (Sig _S _T)  = Sig <$> eval g _S <*> evalUnder g _T
>
> evalHead :: Subs -> Head -> Tm
> evalHead g (V x _)    | Just t <- lookup x g      = t
> evalHead g (M alpha)  | Just t <- lookup alpha g  = t
> evalHead g h                                      = N h B0
>
> evalUnder :: (Fresh m , Applicative m) => Subs -> Bind Nom Tm -> m (Bind Nom Tm)
> evalUnder g b = do
>   (x , t) <- unbind b
>   bind x <$> eval g t

The |(%%)| operator reduces a redex (a term with an eliminator) to
normal form: this re-invokes hereditary substitution when a
$\lambda$-abstraction meets an application.

> (%%) :: (Fresh m , Applicative m) => Tm -> Elim -> m Tm
> L b       %%  (A a)     = do
>   (x , t) <- unbind b
>   eval [(x, a)] t
> PAIR x _  %%  Hd        = return x
> PAIR _ y  %%  Tl        = return y
> TRUE      %%  If _ t _  = return t
> FALSE     %%  If _ _ f  = return f
> ZE        %%  Fold _P cz cs = return cz
> SU n      %%  Fold _P cz cs = do
>   (m , cs')  <- unbind cs
>   (p , cs'') <- unbind cs'
>   n' <- n %% Fold _P cz cs
>   eval [(m , n) , (p , n')] cs''
> N h e     %%  z         = return $ N h (e :< z)
> t         %%  a         = error "bad elimination"

% of " ++ pp t ++ " by " ++ pp a

I define some convenient abbreviations: |($$)| for applying a function
to an argument, |($*$)| for applying a function to a telescope of
arguments, |inst| for substituting out a single binding and |hd| and
|tl| for the projections from $\Sigma$-types.

> ($$) :: (Fresh m , Applicative m) => Tm -> Tm -> m Tm
> f $$ a = f %% A a
>
> ($*$) :: (Fresh m , Applicative m) => Tm -> Bwd (Nom, Type) -> m Tm
> f $*$ _Gam = foldlM ($$) f (fmap (var . fst) _Gam)
>
> inst :: (Fresh m , Applicative m) => Bind Nom Tm -> Tm -> m Tm
> inst f s = L f $$ s
>
> hd, tl :: (Fresh m , Applicative m) => Tm -> m Tm
> hd  = (%% Hd)
> tl  = (%% Tl) 

%if False

> $(derive[''Tm, ''Can, ''Elim, ''Head, ''Twin])

%endif

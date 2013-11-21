-- The 'unsafeUnbind' usage is ... wait for it ... unsafe :P
--
-- Run with 'runhaskell SubstitutionBug.hs'.

import PatternUnify.Tm
import Common.PrettyPrint
import Common.Names
import Common.BwdFwd
import Control.Monad

egs :: [Tm]
egs = runFreshM $ do
  x0 <- fresh . s2n $ "x"
  x1 <- fresh . s2n $ "x"
  let v0 = V x0 Only
      v1 = V x1 Only
      n0 = N v0 B0
      n1 = N v1 B0
      eg1 = L (bind x0 (L (bind x1 (C (Pair n0 n1)))))
      eg2 = n1
  eg1eg2 <- eg1 $$ eg2
  return $ [ eg1
           , eg2
           , eg1eg2
           -- , eg1 $$ eg2 -- Should be \ x2 . Pair x1 x2 for *fresh* x
           --              -- but it's  \ x1 . Pair x1 x1 instead :P
           ]

main = do
  forM_ egs $ \ e -> do
    putStrLn . show $ e
    putStrLn . pp $ e

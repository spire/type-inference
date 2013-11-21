-- The 'unsafeUnbind' usage is ... wait for it ... unsafe :P
--
-- Run with 'runhaskell SubstitutionBug.hs'.

import PatternUnify.Tm
import Common.PrettyPrint
import Common.Names
import Common.BwdFwd
import Control.Monad

egs :: [(Tm , Tm , Tm)]
egs = runFreshM $ do
  x0 <- fresh . s2n $ "x"
  x1 <- fresh . s2n $ "x"
  x2 <- fresh . s2n $ "x"
  let v0 = V x0 Only
      v1 = V x1 Only
      v2 = V x2 Only
      n0 = N v0 B0
      n1 = N v1 B0
      n2 = N v2 B0
      eg1 = L (bind x0 (L (bind x1 (C (Pair n0 n1)))))
      eg2 = n1
      eg3 = L (bind x0 (L (bind x1 (N v0 (B0 :< A n1 :< A n0)))))
      eg4 = n2
  eg1eg2 <- eg1 $$ eg2
  eg3eg2 <- eg3 $$ eg2
  eg1eg2eg4 <- eg1eg2 $$ eg4
  eg3eg2eg4 <- eg3eg2 $$ eg4
  return $ [ (eg1 , eg2 , eg1eg2)
           , (eg3 , eg2 , eg3eg2)
           , (eg1eg2 , eg4 , eg1eg2eg4)
           , (eg3eg2 , eg4 , eg3eg2eg4)
           -- , eg1 $$ eg2 -- Should be \ x2 . Pair x1 x2 for *fresh* x
           --              -- but it's  \ x1 . Pair x1 x1 instead :P
           ]

main = do
  forM_ egs $ \ (e1 , e2 , e3) -> do
    putStrLn $ show e1 ++ "\n" ++ show e2 ++ "\n=\n" ++ show e3
    putStrLn ""
    putStrLn $ ppp  e1 ++ "\n" ++ ppp  e2 ++ "\n=\n" ++ ppp  e3
    putStrLn ""
    putStrLn ""

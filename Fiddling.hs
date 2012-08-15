{-# LANGUAGE DeriveFunctor, RankNTypes, TypeOperators #-}

module Fiddling where

import Data.Functor
import Control.Monad
import Data.List (intersperse)

--------------------------------------------------------------------------------
data Mu f = Inn { unInn :: f (Mu f) }

foldMu :: Functor f => (f a -> a) -> Mu f -> a
foldMu fAlgebra = loop
    where
       loop = fAlgebra . fmap loop . unInn

--------------------------------------------------------------------------------
-- Eilenberg-Moore algebras
expAlg :: Monad m => (m a -> a) -> (m (b -> a) -> b -> a)
expAlg mAlgebra f b = mAlgebra (f `ap` return b)

------------------------------------------------------------------------------
data MMu f m = In { unIn :: f (m (MMu f m)) }

eFold :: (Monad m, Functor m, Functor f) =>
         (f a -> a)
      -> (m a -> a)
      -> m (MMu f m)
      -> a
eFold fAlgebra mAlgebra =
    mAlgebra . fmap loop
    where
      loop = fAlgebra . fmap mAlgebra . fmap (fmap loop) . unIn

ePara :: (Monad m, Functor m, Functor f) =>
         (f (a, m (MMu f m)) -> a)
      -> (m a -> a)
      -> m (MMu f m)
      -> a
ePara fAlgebra mAlgebra =
    mAlgebra . fmap loop
    where
      loop (In x) =
          fAlgebra $ fmap (\(a,b) -> (mAlgebra a, b)) $ fmap (\x -> (fmap loop x, x)) $ x

------------------------------------------------------------------------------
data ListF a x
    = Nil
    | Cons a x
    deriving (Functor, Show)

eReplicate :: Monad m => Int -> m a -> m (MMu (ListF a) m)
eReplicate 0 generator = return (In Nil)
eReplicate n generator = do
  a <- generator
  return (In (Cons a (eReplicate (n-1) generator)))

--------------------------------------------------------------------------------
eAppend :: (Monad m, Functor m) =>
           m (MMu (ListF a) m)
        -> m (MMu (ListF a) m)
        -> m (MMu (ListF a) m)
eAppend xs ys = eFold fAlgebra join xs
    where
      fAlgebra Nil         = ys
      fAlgebra (Cons a xs) = return (In (Cons a xs))

fold :: (Functor f, Functor m) =>
        (f (m a) -> a)
     -> MMu f m
     -> a
fold fmAlgebra (In x) =
    fmAlgebra $ fmap (fmap (fold fmAlgebra)) $ x

append :: (Monad m, Functor m) =>
          m (MMu (ListF a) m)
       -> m (MMu (ListF a) m)
       -> m (MMu (ListF a) m)
append xs ys = xs >>= fold fmAlgebra
    where
      fmAlgebra Nil         = ys
      fmAlgebra (Cons a xs) = (In . Cons a) <$> xs -- return (In (Cons a (join xs)))

data W a = W String a deriving (Functor, Show)
instance Monad W where
    return       = W ""
    W s1 a >>= f = let W s2 b = f a in W (s1 ++ s2) b

l1 = W "a" (In $ Cons 1 (W "b" (In Nil)))
l2 = W "c" (In $ Cons 2 (W "d" (In Nil)))
l3 = W "e" (In $ Cons 1 (W "f" (In $ Cons 2 (W "g" (In Nil)))))

p :: Show a => W (MMu (ListF a) W) -> String
p (W s (In Nil))         = "(W " ++ s ++ " (In Nil))"
p (W s (In (Cons a xs))) = "(W " ++ s ++ " (In (Cons " ++ show a ++ " " ++ p xs ++ ")))"

append2 :: (Monad m, Functor m) =>
           m (MMu (ListF a) m)
        -> m (MMu (ListF a) m)
        -> m (MMu (ListF a) m)
append2 xs ys = xs >>= \xs' -> fold fmAlgebra xs' ys
    where 
      fmAlgebra Nil         ys = ys
      fmAlgebra (Cons a xs) ys = do f <- xs
                                    return (In (Cons a (f ys)))

-- explicitly recursive version
append3 :: (Monad m, Functor m) =>
           m (MMu (ListF a) m)
        -> m (MMu (ListF a) m)
        -> m (MMu (ListF a) m)
append3 xs ys = do
  In step <- xs
  case step of
    Nil       -> ys
    Cons a xs -> return (In (Cons a (append3 xs ys)))

--------------------------------------------------------------------------------
printAll :: Show a => IO (MMu (ListF a) IO) -> IO ()
printAll = eFold fAlgebra join
    where
      fAlgebra Nil        = return ()
      fAlgebra (Cons a x) = do putStr (show a); putStr "; "; x

--------------------------------------------------------------------------------
-- An example of a free monad
data ReaderF a b x
    = Read  (Maybe a -> x)
    | Yield b
    deriving Functor

run :: (Monad m, Functor m) =>
       m (MMu (ListF a) m)
    -> m (MMu (ReaderF a b) m)
    -> m (Maybe b)
run = eFold fAlgebra (expAlg join)
    where
      fAlgebra Nil         reader = return Nothing
      fAlgebra (Cons a xs) reader = do
        readerStep <- unIn `fmap` reader
        case readerStep of
          Read k  -> xs (k (Just a))
          Yield b -> return (Just b)

runFold :: (Monad m, Functor m) =>
           m (MMu (ListF a) m)
        -> m (MMu (ReaderF a b) m)
        -> m (Maybe b)
runFold s r = s >>= \s' -> fold fmAlgebra s' r
    where
      fmAlgebra Nil        r = return Nothing
      fmAlgebra (Cons a s) r = do
        s' <- s
        In rs <- r
        case rs of
          Read k  -> s' (k (Just a))
          Yield b -> return (Just b)

-- and another 'run' function that recurses on the reader instead of
-- the input stream

run2 :: (Monad m, Functor m) =>
        m (MMu (ListF a) m)
     -> m (MMu (ReaderF a b) m)
     -> m b
run2 input reader = eFold fAlgebra (expAlg join) reader input
    where
      fAlgebra (Read k) input = do
        inputStep <- unIn `fmap` input
        case inputStep of
          Nil           -> k Nothing (return (In Nil))
          Cons a input' -> k (Just a) input'
      fAlgebra (Yield b) input = do
        return b

ofList :: Monad m => [a] -> m (MMu (ListF a) m)
ofList []     = return (In Nil)
ofList (x:xs) = return (In $ Cons x (ofList xs))

ofListIO :: [Int] -> IO (MMu (ListF Int) IO)
ofListIO []     = return (In Nil)
ofListIO (x:xs) = do putStrLn (show x)
                     return (In $ Cons x (ofListIO xs))

toList :: (Functor m, Monad m) => m (MMu (ListF a) m) -> m [a]
toList = eFold fAlgebra join
    where
      fAlgebra Nil        = return []
      fAlgebra (Cons x l) = (x:) <$> l

--------------------------------------------------------------------------------
data ProcessorF a b x
    = Input  (Maybe a -> x)
    | Output b x
    | Stop
    deriving Functor

($$) :: (Monad m, Functor m) =>
        m (MMu (ProcessorF a b) m)
     -> m (MMu (ListF a) m)
     -> m (MMu (ListF b) m)
($$) = applyProc

applyProc :: (Monad m, Functor m) =>
             m (MMu (ProcessorF a b) m)
          -> m (MMu (ListF a) m)
          -> m (MMu (ListF b) m)
applyProc = eFold fAlgebra (expAlg join)
    where
      fAlgebra (Input k)    input = do
        inputStep <- unIn <$> input
        case inputStep of
          Nil           -> k Nothing  (return (In Nil))
          Cons a input' -> k (Just a) input'
      fAlgebra (Output b f) input = do
        return (In $ Cons b (f input))
      fAlgebra Stop         input = do
        return (In Nil)

appendProc :: forall m a b c. (Monad m, Functor m) =>
              m (MMu (ProcessorF a b) m)
           -> m (MMu (ProcessorF b c) m)
           -> m (MMu (ProcessorF a c) m)
appendProc processor1 processor2 =
    eFold fAlgebra (expAlg join) processor2 processor1
    where
      fAlgebra (Input k)    inputProcessor =
          ePara (fAlgebra2 k) join inputProcessor
        --runInput k inputProcessor
      fAlgebra (Output c f) inputProcessor = do
        return (In (Output c (f inputProcessor)))
      fAlgebra Stop         inputProcessor = do
        return (In Stop)

      fAlgebra2 k (Input k')   = return (In (Input $ \x -> fst (k' x)))
      fAlgebra2 k (Output b i) = k (Just b) (snd i)
      fAlgebra2 k Stop         = return (In Stop)

-- FIXME: how to excuse the use of unconstrained recursion here?
proc1 :: Monad m => m (MMu (ProcessorF Int Int) m)
proc1 = return (In $ Input $ \x -> case x of Nothing -> return (In Stop); Just x -> return (In $ Output (x+1) proc1))

proc2 :: Monad m => m (MMu (ProcessorF Int Int) m)
proc2 = return (In $ Input $ \x -> case x of Nothing -> return (In Stop); Just x -> return (In $ Output (x*2) proc2))



{-
      -- Hmm, need some kind of paramorphism?
      runInput k input = do
        inputStep <- unIn <$> input
        case inputStep of
          -- in this case, we use the recursively computed value
          Input k'   -> return (In (Input $ \x -> runInput k (k' x)))
          -- in this case, we don't
          Output b i -> k (Just b) i
          Stop       -> return (In Stop)
-}

--------------------------------------------------------------------------------
-- Also to look at:
--  LL(1) parsing vs. Chunking
--  resource deallocation (with a special monad?) (Use for Kripke predicates?)
--  sorting out the problem with the runInput function above in appendProc (fall back to normal fold? general recursion?)
--  doing something with other shapes of data (some sort of trees, numbering problem?)
--  resource modification/states? (another use for Kripke predicates/indexed types?)
--  stream fusion based approaches, and connection with the coinductive presentation

--------------------------------------------------------------------------------
data TreeF x
    = Node String [x]
    deriving (Show, Functor)

-- annotation monad
data AnnotM a = AM String a deriving Show
instance Monad AnnotM where
    return a = AM "" a
    AM x a >>= f = let AM y b = f a in AM (x++y) b

instance Functor AnnotM where
    fmap = liftM

-- an annotated tree
t :: AnnotM (MMu TreeF AnnotM)
t = AM "a" (In $ Node "node1"
                   [ AM "a" (In $ Node "node2" [])
                   , AM "a" (In $ Node "node3" [])
                   ])

t2 :: AnnotM (MMu TreeF AnnotM)
t2 = AM "b" (In $ Node "nodeX" [])

prTree :: AnnotM (MMu TreeF AnnotM) -> String
prTree (AM x (In (Node nm l))) = 
    "(" ++ nm ++ "{" ++ x ++ "} [" ++ concat (intersperse "," $ map prTree l) ++ "])"

subst :: String
      -> AnnotM (MMu TreeF AnnotM)
      -> AnnotM (MMu TreeF AnnotM)
      -> AnnotM (MMu TreeF AnnotM)
subst ident tree = eFold fAlgebra join
    where
      fAlgebra (Node s l) =
          if s == ident then tree else return (In $ Node s l)

--------------------------------------------------------------------------------
eReverse :: (Monad m, Functor m) => m (MMu (ListF a) m) -> m (MMu (ListF a) m)
eReverse = eFold fAlgebra join
    where
      fAlgebra Nil         = construct Nil
      fAlgebra (Cons a xs) = eAppend xs (construct (Cons a (construct Nil)))

-- want to show that eReverse (eAppend xs ys) == eAppend (eReverse ys) (eReverse xs)

--------------------------------------------------------------------------------
newtype NameGen a = NG { unNG :: Int -> (a, Int) }

instance Monad NameGen where
    return a   = NG $ \i -> (a,i)
    NG c >>= f = NG $ \i -> let (a,i') = c i in unNG (f a) i'

new :: NameGen Int
new = NG $ \i -> (i,i+1)

-- what to do with this? anything useful?
-- 

--------------------------------------------------------------------------------
-- free monads, and coproducts with them
data FMF f a x
    = Var  a
    | Term (f x)
    deriving Functor

newtype FM f a = FM { unFM :: Mu (FMF f a) }

constructMu :: f (Mu f) -> Mu f
constructMu = Inn

instance (Functor f) => Monad (FM f) where
    return x = FM (constructMu (Var x))
    FM c >>= f = FM (foldMu fAlgebra c)
        where
          fAlgebra (Var a)  = unFM (f a)
          fAlgebra (Term x) = constructMu (Term x)

ext :: (Functor f, Monad m) =>
       (forall a. f a -> m a)
    -> FM f a -> m a
ext g (FM c) = foldMu fAlgebra c
    where fAlgebra (Var a)   = return a
          fAlgebra (Term fx) = join (g fx)

unrecurse :: (Functor f, Monad m) =>
             (forall a. FM f a -> m a)
          -> f a
          -> m a
unrecurse g x = g $ FM $ constructMu $ Term $ fmap (unFM . return) x

--------------------------------------------------------------------------------
newtype CoprodM f m a = CPM { unCPM :: m (MMu (FMF f a) m) }

construct :: Monad m => f (m (MMu f m)) -> m (MMu f m)
construct = return . In

constructm :: Monad m => m (m (MMu f m)) -> m (MMu f m)
constructm = join

instance (Functor f, Functor m, Monad m) => Monad (CoprodM f m) where
    return x = CPM $ construct (Var x)
    CPM c >>= f = CPM $ eFold fAlgebra join c
        where
          fAlgebra (Var a)  = unCPM (f a)
          fAlgebra (Term x) = construct (Term x)
-- looks the same!

{-
inj1 :: (Functor f, Monad m) => FM f a -> CoprodM f m a
inj1 (FM x) = CPM $ foldMu construct x
-}

test :: (Functor f, Functor m, Monad m) => f a -> CoprodM f m a
test x = CPM $ construct (Term (fmap (unCPM . return) x))

inj1 :: (Functor f, Functor m, Monad m) => FM f a -> CoprodM f m a
inj1 = ext test

inj2 :: (Functor f, Functor m, Monad m) => m a -> CoprodM f m a
inj2 x = CPM $ constructm (fmap (unCPM . return) x)

caseM :: (Functor f, Functor m, Monad m, Monad m') =>
         (forall a. FM f a -> m' a)
      -> (forall a. m a -> m' a)
      -> CoprodM f m a
      -> m' a
caseM g1 g2 = eFold fAlgebra (join . g2) . unCPM
    where
      fAlgebra (Var a)   = return a
      fAlgebra (Term fx) = join (unrecurse g1 fx)

      mAlgebra = join . g2

--------------------------------------------------------------------------------
newtype (f :.: g) a = C (f (g a))

-- to prove:
-- 1. caseM g1 g2 is always a monad morphism
-- 2. caseM (h . inj1) (h . inj2) = h (proves uniqueness)
-- 3. caseM g1 g2 . inj1 = g1
-- 4. caseM g1 g2 . inj2 = g2


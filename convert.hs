{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
module Main where

import Control.Applicative
import Control.Exception
import Control.Monad
import Data.List (intersperse, sortBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as Set
import Data.String
import qualified Data.Text as T
import qualified Data.Text.Lazy.Builder as TB
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TL
import System.Environment
import Text.Megaparsec
import Text.Megaparsec.Text.Lazy

data SExpr
  = Atom T.Text
  | Compound [SExpr]
  deriving (Show, Eq, Ord)

sexprParser :: Parser SExpr
sexprParser = space >> s
  where
    s :: Parser SExpr
    s = msum
      [ Compound <$> (tok (char '(') *> many s <* tok (char ')'))
      , (Atom . fromString) <$> tok (some (alphaNumChar <|> oneOf "$@?+-/_:*.<>="))
      ]
    tok :: Parser a -> Parser a
    tok p = p <* space

sexprBuilder :: SExpr -> TB.Builder
sexprBuilder (Atom t) = TB.fromText t
sexprBuilder (Compound []) = TB.fromText "()"
sexprBuilder (Compound (x:xs)) = TB.singleton '(' <> sexprBuilder x <> mconcat [TB.singleton ' ' <> sexprBuilder x | x <- xs] <> TB.singleton ')'

showSExpr :: SExpr -> String
showSExpr = TL.unpack . TB.toLazyText . sexprBuilder

showSExprText :: SExpr -> T.Text
showSExprText = TL.toStrict . TB.toLazyText . sexprBuilder

data Proof formula
  = Inference
  { infRule :: T.Text
  , infConclusion :: formula
  , infPremises :: [Proof formula]
  , infAssumptions :: Set formula
  }
  deriving (Eq, Ord, Show)

proofSize :: Proof f -> Int
proofSize p = 1 + sum (map proofSize (infPremises p))

parseProof :: SExpr -> Proof SExpr
parseProof = inferAssumptions . f Map.empty
  where
    f :: Map T.Text SExpr -> SExpr -> Proof SExpr
    f env (Compound [Atom "let", Compound [Compound [Atom v, rhs]], body]) =
      f (Map.insert v rhs env) body
    f env (Compound (rule : args)) =
      Inference
      { infRule = showSExprText rule
      , infConclusion = expand env (last args)
      , infPremises = [f env arg | arg <- init args]
      , infAssumptions = undefined
      }
    f env (Atom x) =
      case Map.lookup x env of
        Just y -> f env y
        Nothing -> error "should not happen"

    expand :: Map T.Text SExpr -> SExpr -> SExpr
    expand env (Atom x) =
      case Map.lookup x env of
        Just y -> expand env y
        Nothing -> Atom x
    expand env (Compound xs) = Compound $ map (expand env) xs

inferAssumptions :: Proof SExpr -> Proof SExpr
inferAssumptions p = (\q -> infAssumptions q `seq` q) $
  case infRule p of
    "hypothesis" -> p{ infAssumptions = Set.singleton (infConclusion p) }
    "lemma"
      | assumptionsToDischarge `Set.isSubsetOf` premiseAssumptions ->
          p'{ infAssumptions = premiseAssumptions `Set.difference` assumptionsToDischarge }
      | otherwise -> error $ "should not happen: " -- ++ (showSExpr $ infConclusion p) ++ " VS " ++ show (Set.map showSExpr premiseAssumptions)
    _ -> p'{ infAssumptions = premiseAssumptions }
  where
    p' = p{ infPremises = [inferAssumptions q | q <- infPremises p] }
    premiseAssumptions = Set.unions [infAssumptions q | q <- infPremises p']
    assumptionsToDischarge =
      case infConclusion p of
        Compound (Atom "or" : xs) -> Set.fromList [neg x | x <- xs]
        x -> Set.singleton (neg x)
    neg (Compound [Atom "not", x]) = x
    neg x = Compound [Atom "not", x]

toTex :: Proof SExpr -> TB.Builder
toTex proof = 
    mconcat ["\\[\n" <> f 0 p <> "\\]\n" | (p,i) <- subproofsWithMultipleOccurences] <>
    ("\\[\n" <> f 0 proof <> "\\]\n")  
  where
    f lv p@Inference{ infConclusion = conclusion }
      | lv > 0
      , Just i <- Map.lookup p subproofsWithMultipleOccurencesMap =
          indent lv <> "\\deduce{" <> escapeSExprMath conclusion <> "}{(" <> TB.fromString (show i) <> ")}\n"
    f lv Inference{ infRule = rule, infConclusion = conclusion, infPremises = premises } =
      indent lv <> "\\infer[" <> escapeText rule <> "]{" <> escapeSExprMath conclusion <> "}" <>
      (if null premises
       then "{}"
       else "{\n" <> mconcat (intersperse (indent (lv+1) <> "&\n") [f (lv+1) p | p <- premises]) <> indent lv <> "}") <>
      "\n"

    indent :: Int -> TB.Builder
    indent level = TB.fromString $ replicate (level * 2) ' '

    escapeText :: T.Text -> TB.Builder
    escapeText x = "\\texttt{" <> TB.fromText (T.concatMap g x) <> "}"
      where
        g '_' = "\\_"
        g '*' = "$*$"
        g c = T.singleton c

    escapeSExprMath :: SExpr -> TB.Builder
    escapeSExprMath x = "\\mbox{" <> escapeText (showSExprText x) <> "}"

    subproofsWithMultipleOccurencesMap :: Map (Proof SExpr) Int
    subproofsWithMultipleOccurencesMap = Map.fromList subproofsWithMultipleOccurences

    subproofsWithMultipleOccurences :: [(Proof SExpr, Int)]
    subproofsWithMultipleOccurences = zip (sortBy (comparing proofSize) ys) [1..]
      where
        ys = [p | (p,xs) <- Map.toList subproofOccurences, Set.size xs > 1, proofSize p > 1]

        subproofOccurences :: Map (Proof SExpr) (Set (Proof SExpr, Int))
        subproofOccurences = f proof
          where
            f x = Map.unionsWith Set.union (map f (infPremises x)) `Map.union`
                  Map.fromListWith Set.union [(y, Set.singleton (x,i)) | (i,y) <- zip [1..] (infPremises x)]


toGraphViz :: Proof SExpr -> TB.Builder
toGraphViz proof =
  "digraph {\n" <>
  mconcat [ TB.fromText name <> " [ shape = \"ellipse\", label = \"" <> sexprBuilder f <> "\" ];\n" | ((f,_),name) <- Map.toList formulaTable ] <>
  mconcat [ TB.fromText name <> " [ shape = \"box\", label = \"" <> TB.fromText (infRule p) <> "\" ];\n" | (p,name) <- Map.toList subproofTable ] <>
  mconcat
    [ TB.fromText name <> " -> " <> TB.fromText (formulaTable Map.! (infConclusion p, infAssumptions p)) <> "\n" <>
      mconcat
        [ TB.fromText (formulaTable Map.! (infConclusion x, infAssumptions x)) <> " -> " <> TB.fromText name <>
          " [ label = \"" <> TB.fromString (show i) <> "\" ];\n"
        | (x,i) <- zip (infPremises p) [(1::Int)..]
        ]
    | (p, name) <- Map.toList subproofTable
    ] <>
  "}\n"
  where
    formulas :: Set (SExpr, Set SExpr)
    formulas = f proof
      where
        f p = Set.insert (infConclusion p, infAssumptions p) $ Set.unions (map f (infPremises p))

    subproofs :: Set (Proof SExpr)
    subproofs = f proof
      where
        f x = Set.insert x $ Set.unions (map f (infPremises x))

    formulaTable :: Map (SExpr, Set SExpr) T.Text
    formulaTable = Map.fromAscList $ zip (Set.toAscList formulas) ["f" <> T.pack (show i) | i <- [(1::Int)..]]

    subproofTable :: Map (Proof SExpr) T.Text
    subproofTable = Map.fromAscList $ zip (Set.toAscList subproofs) ["p" <> T.pack (show i) | i <- [(1::Int)..]]

main :: IO ()
main = do
  [fname] <- getArgs
  t <- TL.readFile fname
  case runParser sexprParser fname t of
    Left err -> throwIO err
    Right s -> do
      let f x = do
            let proof = parseProof x
            TL.putStrLn $ TB.toLazyText (toTex proof)
            TL.putStrLn $ TB.toLazyText (toGraphViz proof)
      case s of
        Compound [Atom "proof", body] -> f body
        Compound xs ->
          case [body | Compound [Atom "proof", body] <- xs] of
            body : _ -> f body
            _ -> error "no proof found"
        _ -> error "no proof found"

-- dvipdfmx -p 110cm,15cm sample1-tex
-- dvipdfmx -p 230cm,15cm sample2-tex

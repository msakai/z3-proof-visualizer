{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
module Main where

import Control.Applicative
import Control.Exception
import Control.Monad
import Data.List (intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
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

data Proof formula
  = Inference
  { infRule :: T.Text
  , infConclusion :: formula
  , infPremises :: [Proof formula]
  }
  deriving (Eq, Ord, Show)

parseProof :: SExpr -> Proof SExpr
parseProof = f Map.empty
  where
    f :: Map T.Text SExpr -> SExpr -> Proof SExpr
    f env (Compound [Atom "let", Compound [Compound [Atom v, rhs]], body]) =
      f (Map.insert v rhs env) body
    f env (Compound (rule : args)) = 
      Inference
      { infRule = TL.toStrict $ TB.toLazyText (sexprBuilder rule)
      , infConclusion = expand env (last args)
      , infPremises = [f env arg | arg <- init args]
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

toTex :: Proof SExpr -> TB.Builder
toTex proof = f 0 proof
  where
    f level (Inference rule conclusion premises) =
        indent <> "\\infer[" <> escapeText rule <> "]{" <> escapeSExprMath conclusion <> "}" <>
        (if null premises
         then "{}"
         else "{\n" <> mconcat (intersperse (indent' <> "&\n") [f (level + 1) p | p <- premises]) <> indent <> "}") <>
        "\n"
      where
        indent = TB.fromString $ replicate (level * 2) ' '
        indent' = TB.fromString $ replicate ((level + 1) * 2) ' '

    escapeText :: T.Text -> TB.Builder
    escapeText x = "\\texttt{" <> TB.fromText (T.concatMap g x) <> "}"
      where
        g '_' = "\\_"
        g '*' = "$*$"
        g c = T.singleton c

    escapeSExprMath :: SExpr -> TB.Builder
    escapeSExprMath x = "\\mbox{" <> escapeText (TL.toStrict $ TB.toLazyText $ sexprBuilder x) <> "}"

toGraphViz :: Proof SExpr -> TB.Builder
toGraphViz proof =
  "digraph {\n" <>
  mconcat [ TB.fromText name <> " [ shape = \"ellipse\", label = \"" <> sexprBuilder f <> "\" ];\n" | (f,name) <- Map.toList formulaTable ] <> 
  mconcat [ TB.fromText name <> " [ shape = \"box\", label = \"" <> TB.fromText (infRule p) <> "\" ];\n" | (p,name) <- Map.toList subproofTable ] <> 
  mconcat
    [ TB.fromText infNodeName <> " -> " <> TB.fromText (formulaTable Map.! con) <> "\n" <>
      mconcat
        [ TB.fromText (formulaTable Map.! infConclusion x) <> " -> " <> TB.fromText infNodeName <>
          " [ label = \"" <> TB.fromString (show i) <> "\" ];\n"
        | (x,i) <- zip premises [(1::Int)..]
        ]
    | (Inference _rule con premises, infNodeName) <- Map.toList subproofTable
    ] <>   
  "}\n"
  where
    formulas :: Set SExpr
    formulas = f proof
      where
        f (Inference _ con xs) = Set.insert con $ Set.unions (map f xs)

    subproofs :: Set (Proof SExpr)
    subproofs = f proof
      where
        f x@(Inference _ _ xs) = Set.insert x $ Set.unions (map f xs)

    formulaTable :: Map SExpr T.Text
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

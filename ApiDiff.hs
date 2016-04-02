{-# LANGUAGE FlexibleContexts #-}
module Main where

import System.Exit
import System.Process
import Console.Options
import Control.Arrow (first)
import Control.Applicative
import Control.Monad
import Data.Char
import Data.List (intercalate)

data ApiElem = ApiData NameVars [String]
             | ApiDataWhere NameVars [String]
             | ApiNewtype NameVars Constr
             | ApiType NameVars TyElem
             | ApiRole Name String
             | ApiFamily Name [VarKind] KindSig
             | ApiClass (Maybe Constraint) NameVarsKind
             | ApiSignature FunctionName (Maybe Constraint) Sig
    deriving (Show,Eq)

newtype Package = Package String
    deriving (Show,Eq)
newtype ModName = ModName String
    deriving (Show,Eq)
newtype Name = Name String
    deriving (Show,Eq)
newtype Var = Var String
    deriving (Show,Eq)
data VarKind = VarNoKind String
             | VarKind String KindSig
    deriving (Show,Eq)

data ApiError = ApiError Package ModName String
    deriving (Show,Eq)

data Api = Api Package ModName [(String, ApiElem)]
    deriving (Show,Eq)

newtype Ty = Ty [TyElem]
    deriving (Show,Eq)
data TyElem = TyCon String
            | TyTuple [TyElem]
            | TyList TyElem
            | TyFun (Maybe Constraint) [TyElem]
            | TyKind Name KindSig
            | TyApp String TyElem
            deriving (Show,Eq)

data Constr = NormalConstr Name TyElem
            | InfixConstr -- FIXME
            | RecordConstr Name [(Name, Sig)]
    deriving (Show,Eq)
data Constraint = Constraint (Maybe ForAll) TyElem
    deriving (Show,Eq)
newtype ForAll = ForAll [VarKind]
    deriving (Show,Eq)
type FunctionName = String

type NameVars = (Name, [Var])
type NameVarsKind = (Name, [VarKind])
type Sig = [TyElem] -- tyelem -> tyelem -> ...

newtype KindSig = KindSig [KindElem]
    deriving (Show,Eq)

data KindElem = KindStar
    deriving (Show,Eq)

parseApiElement :: [Token] -> Either String ApiElem
parseApiElement toks = fst <$> runStream parse ([], toks)
  where
    -------------------------
    -- main parsing functions
    -------------------------
    parse = do
        tok <- anyToken
        case tok of
            Just (TokKeyword "newtype") -> parseNewtype
            Just (TokKeyword "data")   -> parseData 
            Just (TokKeyword "class")  -> parseClass
            Just (TokKeyword "type")   -> parseTypeRole <|> parseTypeFamily <|> parseType
            Just (TokSymbol s)         -> parseSignature s
            Just (TokOp "(")           -> do
                s <- symbol
                op ")"
                parseSignature s
            Just (TokKeyword _)        ->
                error ("unhandled keyword starting: " ++ show tok)
            _                    ->
                error ("unknown token starting: " ++ show tok)

    parseData = context "data" $ do
        ty <- parseNameVars
        return $ ApiData ty []
    parseTypeRole = context "type-role" $ do
        word "role"
        ty <- parseName
        r <- symbol
        return $ ApiRole ty r
    parseTypeFamily = context "type-family" $ do
        word "family"
        ty <- parseName
        vars <- some parseVarKind
        sig <- kindSig
        return $ ApiFamily ty vars sig
    parseClass = context "class" $ do
        c <- (Just <$> parseConstraint) <|> pure Nothing
        n <- parseNameVarsKind
        kw "where"
        return $ ApiClass c n
    parseType = context "type" $ do
        ty <- parseNameVars
        op "="
        e <- tyElem
        return $ ApiType ty e
    parseNewtype = context "newtype" $ do
        ty <- parseNameVars
        op "="
        c <- parseConstructor
        return $ ApiNewtype ty c
    parseSignature s = context "signature" $ do
        op "::"
        c <- (Just <$> parseConstraint) <|> pure Nothing
        sig <- parseSig
        return $ ApiSignature s c sig
        
    ------------------
    -- parsing helpers
    ------------------
    parseSig :: Stream Token Sig
    parseSig = do
        t <- tyElem
        ts <- many (op "->" >> tyElem)
        return (t : ts)
    
    parseNameVars :: Stream Token NameVars
    parseNameVars = context "name-vars" $ do
        s    <- parseName
        vars <- many (Var <$> symbol)
        return $ (s, vars)

    parseNameVarsKind :: Stream Token NameVarsKind
    parseNameVarsKind = context "name-vars-kind" $ do
        s    <- parseName
        vars <- many parseVarKind
        return $ (s, vars)

    parseVarKind =
            (VarNoKind <$> symbol)
        <|> (parens (VarKind <$> symbol <*> kindSig))

    tyElem = context "type-element" $
            (TyApp <$> symbol <*> tyElem)
        <|> (TyCon <$> symbol)
        <|> (TyList <$> list)
        <|> (TyTuple <$> tuple)
        {- <|> kind -}
        <|> fun
    tuple = context "tuple" $ parens (tyElem `sep` op ",")
    list = context "list" $ between (op "[") (op "]") tyElem
    fun = context "fun" $ parens $ do
            c   <- option parseConstraint
            sig <- parseSig
            return $ case (c, sig) of
                (Nothing, [x]) -> x
                (_      , l)   -> TyFun c l
    kind = context "kind" $ parens $ do
        n <- parseName
        ksig <- kindSig
        return $ TyKind n ksig
    kindSig = context "kind-sig" $ do
        op "::"
        e1 <- kindElem
        es <- many (op "->" >> kindElem)
        return $ KindSig (e1 : es)
    kindElem = const KindStar <$> op "*"

    parseConstructor :: Stream Token Constr
    parseConstructor = context "constructor" $ do
            context "normal" (NormalConstr <$> parseName <*> tyElem)
        <|> context "record" (RecordConstr <$> parseName <*> between (op "{") (op "}") (parseField `sep` op ","))

    parseField = context "field" $ do
        n <- parseName
        op "::"
        ty <- parseSig
        return (n, ty)

    parseConstraint = context "constraint" $ do
        fall <- option $ do
            word "forall"
            vars <- some parseVarKind
            op "."
            return $ ForAll vars
        e <- tyElem
        op "=>"
        return (Constraint fall e)
    parseName = context "name" (Name <$> symbol)

    parens f = between (op "(") (op ")") f

    ------------------------
    -- stream to parsing DSL
    ------------------------
    
    kw s = eat (== (TokKeyword s))
    word s = eat (== (TokSymbol s))
    op s   = eat (== (TokOp s))

    symbol = eatRet getSymbol
    anyOp  = eatRet getOp

    option f = (Just <$> f) <|> pure Nothing
    between left right f = context "between" (left *> f <* right)

    sep f separator = context "sep" $ loop []
      where
        loop acc = do
            e <- f
            (separator >> loop (e:acc)) <|> (pure $ reverse $ e : acc)
        
    manyTill f stop = loop []
      where
        loop acc = do
            e <- f
            isStop <- next (maybe True stop)
            if isStop then return $ reverse (e:acc) else loop (e:acc)

    isSymbol = maybe False (const True) . getSymbol
    getSymbol (TokSymbol s) = Just s
    getSymbol _             = Nothing

    isOp = maybe False (const True) . getOp
    getOp (TokOp s) = Just s
    getOp _         = Nothing

getModules :: Package -> IO [ModName]
getModules (Package pkg) = do
    let opts = ["field", pkg, "exposed-modules", "--simple-output"]
    (ec, out, err) <- readProcessWithExitCode "ghc-pkg" opts ""
    if ec == ExitSuccess
        then return $ map ModName $ words out
        else error ("cannot get modules for : " ++ pkg)

getAPI :: Package -> ModName -> IO (Either ApiError Api)
getAPI p@(Package pkg) m@(ModName modName) = do
    let opts = ["-hide-all-packages"
               , "-XNoImplicitPrelude"
               , "-package", pkg
               , "-e"
               , ":browse " ++ modName
               ]
    putStrLn ("ghc " ++ intercalate " " opts)
    (ec, out, err) <- readProcessWithExitCode "ghc" opts ""
    if ec == ExitSuccess
        then return $ Right $ Api p m (toEnts out)
        else return $ Left $ ApiError p m err
  where
    toEnts = map (\x -> (x, throwParseError x . parseApiElement . tokenize $ x)) . map (unlines . map snd) . groupByIndent [] . map indentLevel . lines

    throwParseError s (Left err) = error (show err ++ "\n" ++ s)
    throwParseError _ (Right r)  = r

    groupByIndent :: [(Int, String)] -> [(Int, String)] -> [[(Int, String)]]
    groupByIndent acc [] = [reverse acc]
    groupByIndent acc (x:xs)
        | fst x > 0  = groupByIndent (x:acc) xs
        | null acc   = groupByIndent [x] xs 
        | otherwise  = (reverse acc) : groupByIndent [x] xs
{-
    groupByIndent acc [] = [unlines $ reverse acc]
    groupByIndent acc (x:xs)
        | isSpace (head x) = groupByIndent (x:acc) xs
        | null acc         = groupByIndent [x] xs 
        | otherwise        = (unlines $ reverse acc) : groupByIndent [x] xs

    groupIndent :: Int -> [..] -> [(Int, String)] -> [[(Int, String)]]
    groupIndent lvl acc [] = [reverse acc]
    groupIndent lvl acc l =
        let (grp1, r) = span ((>= lvl) . fst) l
         in grp1 : groupIndent
    block :: [(Int, String)] -> [Block]
    block l = doGroup 0 l
      where
        doGroup :: Int -> [..] -> [(Int, String)] -> [ContentOrSub [(Int, String)]]
        doGroup []     = []
        doGroup (x:xs) =
            let level = fst x
            let (sm, after) = span ((>=) level) . fst) l
             in BlockSub (doClass level sm) : doGroup after
-}

    indentLevel :: String -> (Int, String)
    indentLevel s = let (heading, s') = break (/= ' ') s in (length heading, s')

newtype Block = Block [ContentOrSub Block]
                   deriving (Show,Eq)
data ContentOrSub a =
      BlockContent String
    | BlockSub a
    deriving (Show,Eq)

main = defaultMain $ do
    package <- argument "package" Right
    action $ \toParam -> do
        let pkg = Package (toParam package)
        mods <- getModules pkg
        forM_ mods $ \m -> do
            r <- getAPI pkg m
            case r of
                Right (Api p (ModName m) out) -> putStrLn "" >> putStrLn ("[[[ " ++ m ++ " ]]]") >> mapM_ (putStrLn . ((++) "> ") . show) out
                Left _ -> return ()

------------------------------------------------------------------------
-- Stream generic parser
------------------------------------------------------------------------

newtype Stream elem a = Stream { runStream :: ([String],[elem]) -> Either String (a, ([String], [elem])) }

instance Functor (Stream elem) where
    fmap f s = Stream $ \e1 -> case runStream s e1 of
        Left err     -> Left err
        Right (a,e2) -> Right (f a, e2)
instance Applicative (Stream elem) where
    pure  = return
    fab <*> fa = Stream $ \e1 -> case runStream fab e1 of
        Left err      -> Left err
        Right (f, e2) -> either Left (Right . first f) $ runStream fa e2
instance Alternative (Stream elem) where
    empty     = Stream $ \_  -> Left "empty"
    f1 <|> f2 = Stream $ \e1 -> either (\_ -> runStream f2 e1) Right $ runStream f1 e1
instance Monad (Stream elem) where
    return a  = Stream $ \e1 -> Right (a, e1)
    ma >>= mb = Stream $ \e1 -> either Left (\(a, e2) -> runStream (mb a) e2) $ runStream ma e1

eatRet :: Show elem => (elem -> Maybe a) -> Stream elem a
eatRet predicate = Stream $ \(ctx, el) ->
    case el of
        []   -> Left ("empty stream " ++ showCtx ctx)
        x:xs ->
            case predicate x of
                Just a  -> Right (a, (ctx, xs))
                Nothing -> Left ("unexpected atom got: " ++ show x ++ " " ++ (show xs) ++ showCtx ctx)

eat :: Show elem => (elem -> Bool) -> Stream elem ()
eat f = eatRet (\e -> if f e then Just () else Nothing)

-- | check if next element match something. doesn't consume anything
next :: (Maybe elem -> a) -> Stream elem a
next predicate = Stream $ \(ctx, el) ->
    case el of
        []   -> Right (predicate Nothing, (ctx, el))
        x:xs -> Right (predicate $ Just x, (ctx, el))

anyToken :: Stream elem (Maybe elem)
anyToken = Stream $ \(ctx, el) ->
    case el of
        []   -> Right (Nothing, (ctx, el))
        x:xs -> Right (Just x, (ctx, xs))

pattern :: ([elem] -> Maybe (a,[elem])) -> Stream elem a
pattern predicate = Stream $ \(ctx, el) ->
    case el of
        [] -> Left ("empty stream: pattern: " ++ showCtx ctx)
        l  -> case predicate l of
                -- fixme 'reml' could be a different stream, a bit weird
                Just (a, reml) -> Right (a, (ctx, reml))
                Nothing        -> Left ("pattern: failed")

context :: String -> Stream elem a -> Stream elem a
context s f = Stream $ \(ctx, el) -> runStream f (s:ctx, el)

showCtx :: [String] -> String
showCtx l = "  => context = " ++ (intercalate " -> " $ reverse l)

------------------------------------------------------------------------
-- Micro Tokenizer
------------------------------------------------------------------------

data Token =
      TokInt String
    | TokString String
    | TokKeyword String
    | TokSymbol String
    | TokOp String
    deriving (Show,Eq)

tokenize :: String -> [Token]
tokenize all = atomize all
  where
    atomize []         = []
    atomize l@(x:xs)
        | isDigit x    = eatConstruct l TokInt isDigit
        | isSpace x    = atomize xs
        | isGroup x    = TokOp [x] : atomize xs -- eatConstruct l TokOp isOperator
        | isOperator x = eatConstruct l TokOp isOperator
        | x == '"'     = eatString [] xs
        | isAlpha x    = eatConstruct l symbolOrKeyword (\x -> isAlphaNum x || isOperator x) -- x `elem` "_-:.")
        | otherwise    = error ("unknown character tokenizing : " ++ show x ++ "\n" ++ all)
    symbolOrKeyword s
        | s `elem` keywords = TokKeyword s
        | otherwise         = TokSymbol s 

    keywords = ["class", "type", "newtype", "data", "where"]

    isGroup    = flip elem "(){}[]"
    isOperator = flip elem "=!?/&|<>*~_-+:,.'#"
  
    eatConstruct l constr f =
        let (xs1, xs2) = break (not . f) l
         in constr xs1 : atomize xs2
    eatString acc []             = error ("unterminated string: " ++ show ('"' : reverse acc))
    eatString acc ('"':xs)       = TokString (reverse acc) : atomize xs
    eatString acc ('\\':'"':xs)  = eatString ('"' : acc) xs
    eatString acc ('\\':'\\':xs) = eatString ('\\': acc) xs
    eatString acc ('\\':xs)      = eatString ('\\': acc) xs
    eatString acc (x:xs)         = eatString (x : acc) xs


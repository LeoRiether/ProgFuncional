module Typechecer where

--------------------------------------------------------------------------------
--              Vários cases nesse módulo foram reescritos para               --
--        utilizarem ferramentas monádicas (do notation, >>, >>=, ...)        --
--------------------------------------------------------------------------------

import AbsLI
import Prelude hiding (lookup)
import PrintLI

data R a = OK a | Erro String
         deriving (Eq, Ord, Show, Read)

instance Functor R where
    fmap f (OK x) = OK (f x)
    fmap f (Erro x) = Erro x

instance Applicative R where
    pure f = OK f

    (<*>) (OK f) (OK x) = OK (f x)
    (<*>) (OK f) (Erro e) = Erro e
    (<*>) (Erro e) _ = Erro e

instance Monad R where
    (>>=) (OK x) f = f x
    (>>=) (Erro x) _ = Erro x

    return x = OK x

-- map_err
(~>) (OK x) _f = OK x
(~>) (Erro msg) f = Erro (f msg)


isError e = case e of
    OK _ -> False
    Erro _ -> True


typeCheckP :: Program -> [R Environment]
typeCheckP (Prog fs) =
  let environment = updatecF ([], []) fs
   in case environment of
        OK env -> map (typeCheckFF env) fs
        Erro msg -> [Erro msg]

typeCheckFF :: Environment -> Function -> R Environment
typeCheckFF environment f@(Fun tR id decls stms) =
  if (deadCodeFree stms)
    then if (tR /= Tvoid)
           then if (checkExecutionPathExhaustion stms)
                  then typeCheckF environment f
                  else Erro "nem todo caminho de execucao tem comando return"
           else typeCheckF environment f
    else Erro "Ha deadcode no programa!"

{-
As funcoes "checkExecutionPathExhaustion" e "checkExecutionPathExhaustionS" colaboram
para checar se todo possivel fluxo de execucao do programa termina em comando "return",
em cujo caso a primeira funcao retorna true.
-}

checkExecutionPathExhaustion :: [Stm] -> Bool
checkExecutionPathExhaustion [] = False
checkExecutionPathExhaustion (s:stms) = if (checkExecutionPathExhaustionS s)
                                             then (stms == [])
                                             else (checkExecutionPathExhaustion stms)
checkExecutionPathExhaustionS :: Stm -> Bool
checkExecutionPathExhaustionS x = case x of
    SReturn exp -> True
    SAss id exp -> False
    SDec (Dec tp id) -> False
    CDec tp id exp -> False
    SBlock stms -> checkExecutionPathExhaustion stms
    SWhile exp stm -> checkExecutionPathExhaustionS stm
    SIf exp stmT stmE ->
      (checkExecutionPathExhaustionS stmT) &&
      (checkExecutionPathExhaustionS stmE)

deadCodeFree :: [Stm] -> Bool
deadCodeFree [] = True
deadCodeFree (s:stms) =
  if (deadCodeFreeS s)
    then if (checkExecutionPathExhaustionS s)
           then (stms == [])
           else (deadCodeFree stms)
    else False

deadCodeFreeS  :: Stm -> Bool
deadCodeFreeS   x = case x of
                      SReturn exp -> True
                      SAss id exp -> True
                      SDec (Dec tp id) -> True
                      CDec tp id  exp -> True
                      SBlock stms -> deadCodeFree stms
                      SWhile exp stm -> deadCodeFreeS stm
                      SIf exp stmT stmE -> (deadCodeFreeS stmT) && (deadCodeFreeS stmE)



typeCheckF ::  Environment -> Function -> R Environment
typeCheckF environment (Fun tR id decls stms) = tk newEnvironment (SBlock stms) tR
                                                  where typeBindings = map (\(Dec tp id) -> (id,(tp,"not constant"))) decls
                                                        newEnvironment = pushB  typeBindings environment


tk :: Environment -> Stm -> Type -> R Environment


tk environment x tR =
  case x of
-- SDecls tp id []  ->
-- cDec@(SDecls tp id (i:is)) ->
-- cAssInit@(SInit tp id exp)  ->
-- cDWhile@(SDWhile stm exp) ->
    cDec@(CDec tp id exp) ->
      let r = updateShallowTypeA environment id (tp, "constant")
       in case r of
            OK env ->
              let r1 = tinf env exp
               in case r1 of
                    OK x ->
                      let r2 = tke env (EVar id) x
                       in case r2 of
                            OK env -> OK env
                            Erro msg ->
                              Erro (msg ++ " no comando: " ++ printTree cDec)
                    Erro msg -> Erro (msg ++ " no comando: " ++ printTree cDec)
            Erro msg -> Erro (msg ++ " no comando: " ++ printTree cDec)
    SReturn exp -> tke environment exp tR
    cAss@(SAss id exp) ->
      if ((lookupDeepTypeA environment id) /= "constant")
        then let r = tinf environment exp
              in case r of
                   OK x ->
                     let r2 = tke environment (EVar id) x
                      in case r2 of
                           OK env -> OK env
                           Erro msg ->
                             Erro (msg ++ " no comando: " ++ printTree cAss)
                   Erro msg -> Erro (msg ++ " no comando: " ++ printTree cAss)
        else Erro
               ("@typechecker: " ++
                show id ++
                " eh constante e nao pode ser redefinida no comando: " ++
                printTree cAss)
    SBlock [] -> OK environment
    SBlock (cDec@(SDec (Dec tp id)):stms) ->
        updateShallowType environment id tp
        >>= \env -> tk env (SBlock stms) tR
        ~> \msg -> (msg ++ " no comando: " ++ printTree cDec)
    SBlock (sb@(SBlock bls):stms) ->
        tk (push environment) sb tR
        >> tk environment (SBlock stms) tR
        ~> \msg -> (msg ++ " no comando: " ++ printTree sb)
    SBlock (s:stms) ->
        tk environment s tR
        >>= \env -> tk env (SBlock stms) tR
    cWhile@(SWhile exp stm) ->
        tke environment exp Tint
        >> tk environment stm tR
        ~> \msg -> (msg ++ " no comando: " ++ printTree cWhile)
    cIf@(SIf exp stmT stmE) ->
        tke environment exp Tint
        >> tk environment stmT tR
        >> tk environment stmE tR
        ~> \msg -> msg ++ " no comando: " ++ printTree cIf

tke :: Environment -> Exp -> Type -> R Environment
tke environment exp tp = do
    tipo <- tinf environment exp
    if (tipo == tp)
        then OK environment
        else Erro (" @typechecker:  A expressao " ++
                  printTree exp ++
                  " tem tipo " ++
                  printTree tipo ++ " mas o tipo esperado eh " ++ printTree tp)

combChecks :: Environment -> Exp -> Exp -> Type -> R Type
combChecks environment exp1 exp2 tp =
    tke environment exp1 tp
    >> tke environment exp2 tp
    >> return tp

tinf :: Environment -> Exp -> R Type
tinf environment x =
  case x of
    ECon exp0 exp -> combChecks environment exp0 exp TStr
    EAdd exp0 exp -> combChecks environment exp0 exp Tint
    ESub exp0 exp -> combChecks environment exp0 exp Tint
    EMul exp0 exp -> combChecks environment exp0 exp Tint
    EDiv exp0 exp -> combChecks environment exp0 exp Tint
    EOr exp0 exp -> combChecks environment exp0 exp Tbool
    EAnd exp0 exp -> combChecks environment exp0 exp Tbool
    ENot exp ->
      let r = tke environment exp Tbool
       in case r of
            OK _ -> OK Tbool
            Erro msg -> Erro msg
    EStr str -> OK TStr
    ETrue -> OK Tbool
    EFalse -> OK Tbool
    EInt n -> OK Tint
    EVar id -> lookupDeepType environment id
    Call id lexp ->
        OK Tbool
      -- do
      --   let parameterTypes = map (\(Dec tp _) -> tp) decls in
      --   let tksArgs = zipWith (tke environment) lexp parameterTypes in
      --   let isThereError l =
      --         filter
      --           (== False)
      --           (map
      --              (\e ->
      --                 (let r2 = e
      --                   in case r2 of
      --                        OK _ -> True
      --                        Erro _ -> False))
      --              l) in
      --  TFun (Fun tipoRetorno _ decls stms) <- lookupShallowFunction environment id
      --  if (length decls == length lexp)
      --  then if (isThereError tksArgs /= [])
      --       then Erro " @typechecker: chamada de funcao invalida"
      --       else OK tipoRetorno
      --  else Erro " @typechecker: tamanhos diferentes de lista de argumentos e parametros"

type Annotation = String
type Environment = ([RContext],RContext)
type RContext = [(Ident,(Type,Annotation))]

pushB :: RContext -> Environment -> Environment
pushB typeBindings (sc,fnCtx) =  (  typeBindings : sc, fnCtx)

push :: Environment -> Environment
push (sc,fnCtx) = ([]:sc,fnCtx)

pop :: Environment -> Environment
pop ((s:scs),fnCtx) = (scs,fnCtx)

lookupDeepTypeA :: Environment -> Ident -> Annotation
--lookupDeepType ([],fnCtx) id = Erro (printTree id ++ " nao esta no contexto. ")
lookupDeepTypeA ((s:scs),fnCtx) id =  let r = lookupShallow s id in
                                           case r of
                                              OK (_,a) -> a
                                              Erro _ -> lookupDeepTypeA (scs,fnCtx) id

lookupDeepType :: Environment -> Ident -> R Type
lookupDeepType ([],fnCtx) id = Erro ("@typechecker: " ++ printTree id ++ " nao esta no contexto. ")
lookupDeepType ((s:scs),fnCtx) id =  let r = lookupShallow s id in
                                         case r of
                                            OK (tp,_) -> OK tp
                                            Erro _ -> lookupDeepType (scs,fnCtx) id

lookupShallowFunction :: Environment -> Ident -> R Type
lookupShallowFunction (sc,fnCtx) id =  let r =(lookupShallow fnCtx id) in
                                         case r of
                                            OK (tp,_) -> OK tp
                                            Erro msg -> Erro msg


lookupShallow :: RContext -> Ident -> R (Type,Annotation)
lookupShallow [] s = Erro ("@typechecker: " ++ printTree s ++ " nao esta no contexto. ")
lookupShallow ((i,v):cs) s
   | i == s = OK v
   | otherwise = lookupShallow cs s

updateShallowTypeA :: Environment -> Ident -> (Type,Annotation) -> R Environment
updateShallowTypeA  ([],fnCtx) id (tp,a)     = OK ([[(id,(tp,a))]],fnCtx)
updateShallowTypeA  ((s:sc),fnCtx) id (tp,a) = let r = updateShallowA s id (tp,a)  in
                                                     case r of
                                                        OK cxt -> OK (cxt:sc,fnCtx)
                                                        Erro msg -> Erro msg

updateShallowA :: RContext -> Ident -> (Type,Annotation) -> R RContext
updateShallowA context id (tp,a) = if (elem id (map fst context))
                                     then Erro "@typechecker: tipo ja definido no contexto de tipos"
                                     else OK ((id,(tp,a)):context)

updateShallowType :: Environment -> Ident -> Type -> R Environment
updateShallowType ([],fnCtx) id tp = OK ([[(id,(tp,"not constant"))]],fnCtx)
updateShallowType ((s:sc),fnCtx) id tp = let r = updateShallowA s id (tp,"not constant")  in
                                             case r of
                                                OK cxt -> OK (cxt:sc,fnCtx)
                                                Erro msg -> Erro msg

updatecF :: Environment -> [Function] -> R Environment
updatecF e [] = OK e
updatecF (sc,c) (f@(Fun tp id params stms):fs) = let r = updateShallowA c id ((TFun f),"constant") in
                                                   case r of
                                                     OK ctx -> updatecF (sc,ctx) fs
                                                     Erro msg -> Erro msg


import chorlean.Choreo2

-- example from: Choral: Object-Oriented Choreographic Programming
-- 3.1 Distributed authentication


inductive Location
| client | service | IP
deriving Repr, Fintype

instance : FinEnum Location :=
  FinEnum.ofEquiv _ (proxy_equiv% Location).symm

open Location



inductive IPEff: Type -> Type 1
| createToken: IPEff String
| check_hash: String -> IPEff Bool

instance: MonadLift IPEff IO where
  monadLift x := match x with
    | .createToken => return "valid token"
    | .check_hash s => CmdInputEff.readBool (.some "is the hash [{s}] correct? (apply db lookup here)")


structure Credentials where
  username: String
  password: String

inductive ClientEff: Type -> Type 1
| prompt_credentias: ClientEff Credentials


instance: MonadLiftT ClientEff IO where
  monadLift x := match x with
    | .prompt_credentias => do
      let username <- CmdInputEff.readString ("enter your username")
      let password <- CmdInputEff.readString ("enter your password")
      return {username, password}

-- instance: MonadLiftT ClientEff (Freer CmdInputEff) where
--   monadLift x := match x with
--     | .prompt_credentias => do
--       let username <- CmdInputEff.readString ("enter your username")
--       let password <- CmdInputEff.readString ("enter your password")
--       return {username, password}

instance sig: LocSig Location where
  sig x := match x with
    | client =>  ClientEff ⨳ LogEff
    | service =>  LogEff
    | IP => IPEff ⨳ LogEff
  executable x := match x with
    | client =>  inferInstance
    | service =>  inferInstance
    | IP => inferInstance


def calcHash (salt: String) (pwd: String): String := (salt ++ pwd).dropRight 1

def add_salt (s:String): String := "salty " ++ s

open LogEff
open IPEff

def authenticate (ep:Location) (creds: Credentials @ client # ep):
  Choreo ep (Option ((String @ client # ep) × (String @ service # ep))):= do


  have: MonadLift IPEff (IPEff ⨳ LogEff) := inferInstance


  let pw <- locally client do return (⤉creds).password
  locally service do info "hello service"
  let username <- locally client do return (⤉creds).username
  let username' <- username ~> IP
  let salt <- locally IP do return add_salt (⤉username')
  let salt <- salt ~> client
  let hash <- locally client do return (calcHash (⤉salt) (⤉pw))
  let hash <- hash ~> IP
  let valid <- locally IP do check_hash (⤉hash)

  branch valid fun
  | true => do
    let token <- locally IP do IPEff.createToken
    let token_c <- token ~> client
    let token_s <- token ~> service
    return (token_c, token_s)
  | false =>
    return none


def sso_auth (ep: Location): Choreo ep (Option ((String @ client # ep) × (String @ service # ep))):= do

  have: MonadLift ClientEff (ClientEff ⨳ LogEff) := inferInstance

  let creds: Credentials @ client <- locally client do ClientEff.prompt_credentias
  authenticate ep creds

def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let ep_opt := FinEnum.ofString? mode

  if h: (ep_opt.isSome) then
    let ep := ep_opt.get h
    let net <- init_network ep
    let epp := EPP ep net



    let r <- (sso_auth ep)
    return ()
  else
    IO.println s!"{mode} is no valid endpoint"
    return ()

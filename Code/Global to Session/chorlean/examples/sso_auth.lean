import chorlean.Choreo

-- example from: Choral: Object-Oriented Choreographic Programming
-- 3.1 Distributed authentication


def sso_cfg := gen_cfg
  [
    (("client", "IP"), sym),
    (("service", "IP"), sym)
  ]

structure Credentials where
  username: String @ "client"
  password: String @ "client"



def createToken: local_prog String "IP"
| _ => do
  return "valid token"

def calcHash (salt: String @"client") (pwd: String @"client"): local_prog String "client"
| un => do
  return ((un salt) ++ (un pwd)).dropRight 1

def add_salt (s:String): String := "salty " ++ s


def authenticate (creds: Credentials): Choreo (Option ((String @"client") × (String @"service"))):= do
  let pw <- compute "client" fun un => (un creds.password)
  let _ <- locally "service" fun _ => do
    IO.println "hello service"
  let username <- locally "client" fun un => return (un creds.username)
  let username' <- username ~> "IP"
  let salt <- locally "IP" fun un => return add_salt (un username')
  let salt <- salt ~> "client"
  let hash <- locally "client" (calcHash salt pw)
  let hash <- hash ~> "IP"
  let valid <- locally "IP" fun un => do
    IO.println s!"is the following hash correct? (y/n)\n{un hash}"
    return <- IO.getBool
  branch valid fun
  | true => do
    let token <- locally "IP" createToken
    let token_c <- token ~> "client"
    let token_s <- token ~> "service"
    return (token_c, token_s)
  | false =>
    return none

def authenticate_old (creds: Credentials): Choreo (Option ((String @"client") × (String @"service"))):= do
  let pw <- compute "client" fun un => (un creds.password)
  let _ <- locally "service" fun _ => do
    IO.println "hello service"
  let username <- "client" ~> "IP" pure fun un => (un creds.username)
  let salt <- "IP" ~> "client" ## fun un => return add_salt (un username)
  let hash <- "client" ~> "IP" ## (calcHash salt pw)
  let valid <- locally "IP" fun un => do
    IO.println s!"is the following hash correct? (y/n)\n{un hash}"
    return <- IO.getBool
  branch valid fun
  | true => do
    let token <- locally "IP" createToken
    let token_c <- token ~> "client"
    let token_s <- token ~> "service"
    return (token_c, token_s)
  | false =>
    return none

def sso_auth: Choreo (Option ((String @"client") × (String @"service"))):= do
  let username <- locally "client" fun _ => do
    IO.println "enter your username"
    return <- IO.getLine
  let password <- locally "client" fun _ => do
    IO.println "enter your username"
    return <- IO.getLine

  let creds: Credentials := {username, password}
  authenticate creds

def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network sso_cfg mode
  IO.println (s!"starting sso exmample")
  let res <- ((sso_auth).epp mode).run mode net

  IO.println s!"res: {res}"

  return ()

import Test.my_utils
import chorlean.Network

inductive LocVal (α: Type) (locs: List String) where
| Wrap: α -> LocVal α locs
| Empty: LocVal α locs





infixl:55 "@" => LocVal

instance [Serialize a]: ToString (a @ l) where
  toString := fun x => match x with
    | .Wrap v => toString v ++ "@" ++ toString l
    | .Empty => "Empty"

def wrap {a} (v:a) (l: List String): a @ l:=
  LocVal.Wrap v


def exists_locally: LocVal a l -> Bool
| LocVal.Wrap _ =>  true
| LocVal.Empty => false


def unwrap (lv: a @ l) (_ex: exists_locally lv :=sorry):  a := match lv with
| LocVal.Wrap v =>  v

def Unwrap (l:String) :=   {a:Type} -> {locs: List String} -> (p:locs.contains l :=by decide) -> a @ locs -> a

--def test44 (locs: List String): Unwrap loc  :=  fun x ls => unwrap (locs:=ls)




mutual
  inductive ChorEff: Type -> Type 2 where
  | Send_recv [Serialize a]: a @ owners -> (receiver:String) -> ChorEff (a @ (owners ++ [receiver]))
  | Local (loc: String) : (Unwrap loc -> IO a) -> ChorEff (a @ [loc])
  | Calc (loc: String) {locs: List String} (_ex: locs.contains loc:= by decide) :  (Unwrap loc -> a) -> ChorEff (a @ [loc])
  | Cond [Serialize a] {owners: List String}: a @ owners -> (a -> Choreo b) ->  (_ex: owners.length >= 1 := by decide) -> ChorEff b

  inductive Choreo: Type -> Type 2  where
  | Do :  ChorEff b -> (b -> Choreo a) -> Choreo a
  | Return: a -> Choreo a
end

#check Choreo

def toChoreo (eff: ChorEff a) : Choreo a :=
   Choreo.Do eff (Choreo.Return)

def send_recv {a:Type} [Serialize a] (vl: a @ owners) (receiver:String) (_dont_send_to_yourself: ! owners.contains receiver := by decide):= toChoreo (ChorEff.Send_recv vl receiver)
def locally (loc: String)   (comp: (Unwrap loc ) -> IO b) := toChoreo (ChorEff.Local loc comp)
--def compute (loc: String) {locs: List String} (_ex: locs.contains loc:= by decide) (comp: (Unwrap loc) -> b) := toChoreo (ChorEff.Calc comp (_ex := _ex))
def branch {a:Type} [Serialize a] (lv: a @ owners) (_ex: owners.length >= 1 := by decide) (cont: a -> Choreo b):= toChoreo (ChorEff.Cond lv cont (_ex:=_ex))


infixl:55 "~>" => send_recv

def Choreo.bind: Choreo α → (α → Choreo β) → Choreo β
  | Choreo.Do eff next, next' => Choreo.Do eff (fun x => bind (next x) next')
  | Choreo.Return v, next' => next' v
decreasing_by sorry

instance: Monad Choreo where
  pure x := Choreo.Return x
  bind  := Choreo.bind


mutual
  def ChorEff.epp: ChorEff a -> String -> Network a
  | ChorEff.Send_recv lv receiver (owners:=owners), l => do
    if j:(owners.length >= 1) then
      if (owners.contains l) then
        let sender := owners[0]
        if(sender == l) then
          send receiver (unwrap lv)
          return .Empty

        else if (receiver == l) then
          let response <- (recv sender)
          return wrap response (owners ++ [receiver])
        else
          return .Empty
      else
        return .Empty
    else
      return .Empty
  | ChorEff.Local l1 comp, l2 => do
    if j:( l1 == l2) then
      let res <- run (comp (unwrap ) )
      return wrap res [l1]
    else
      return .Empty
  | ChorEff.Calc l1 _proof comp (locs:=locs), l2 => do
    if j:( l1 == l2) then
      let res := (comp (unwrap))
      return wrap res [l1]
    else
      return .Empty
  | ChorEff.Cond lv fn non_empty_p (owners:=owners), loc => do
    let sender := owners[0]'non_empty_p
    if (owners.contains loc) then
      if(sender == loc) then
        broadcast_except owners (unwrap lv)
        (fn (unwrap lv)).epp loc
      else
        (fn (unwrap lv)).epp loc
    else
      let choice <- (recv sender)
      (fn choice).epp loc



  def Choreo.epp: Choreo a -> String -> Network a
  | Choreo.Return v, _ => Network.Return v
  | Choreo.Do eff next, loc => do
    let res <- (eff.epp loc)
    Choreo.epp (next res) loc

end
decreasing_by sorry --TODO



def bookseller_cfg := local_cfg ["buyer", "seller"] 3333


def book_seller: Choreo (Option (String @ ["buyer", "seller"])):= do

  let budget := wrap 150 ["buyer"]
  let aaaa := wrap 150 ["buybee"]

  let title <- locally  "buyer"  (fun un  => do
    IO.println "enter a book title:"
    let stdin <- IO.getStdin
    let str <-stdin.getLine
    let wrapped :=  (wrap 150 ["buybee2adsihi"])
    let temp := un  wrapped
    return str.dropRight 1
  )
  let title' <- title ~> "seller"

  let nor_title := unwrap title'

  let price <- compute "seller" fun un => if (un title') == "Faust" then 100 else 200
  let price <- price ~> "buyer"

  let _ <- locally "seller" (fun un => do
    IO.println s!"got book title: {un title'}"

  )
  let decision: LocVal Bool "buyer" <- compute "buyer" fun un => (un budget >= un price)

  branch decision fun
  | true => do
    let date <- locally "seller" (fun _ => do
      IO.println "enter the delivery date:"
      let stdin <- IO.getStdin
      return <- stdin.getLine
    )
    let date <- date ~> "buyer"
    return some date
  | false => do

    let _ <- locally "seller" (fun _un => do
      IO.println s!"the customer declined the purchase"
    )
    let _ <- locally "buyer" (fun un => do
      IO.println s!"{un title} has a price of {un price} exceeding your budget of {un budget}!"
    )
    return none


def main (args : List String): IO Unit := do
  let mode := args.get! 0
  let net <- init_network bookseller_cfg mode
  let res <- ((book_seller).epp mode).run mode net
  IO.println (s!"res: {res}")
  return ()

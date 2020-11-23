#load "nums.cma";;

open Big_int;;

type ide = Ide of string;;

type exp =
 Val of ide
| Eint of int
| Echar of char
| Ebigint of int list
| True
| False
| Empty
| Sum of exp * exp
| Diff of exp * exp
| Times of exp * exp
| Bigsum of exp * exp
| Bigdiff of exp * exp
| Bigtimes of exp * exp
| And of exp * exp
| Or of exp * exp
| Not of exp
| Toint of exp
| Tobigint of exp
| Eq of exp * exp
| Less of exp * exp
| Bigless of exp * exp
| Charless of exp * exp
| Cons of exp * exp
| Head of exp
| Tail of exp
| Fst of exp
| Snd of exp
| Epair of exp * exp
| Ifthenelse of exp * exp * exp
| Let of ide * exp * exp
| Fun of ide * exp
| Appl of exp * exp
| Rec of ide * exp;;

type eval =
Undefined
| Int of int
| Bool of bool
| Bigint of int list
| Char of char
| List of eval list
| Pair of eval * eval
| Closure of exp * env
and
env = ide -> eval;;

 type etype =
   TBool
  |TInt
  |TChar
  |TBigint
  |TVar of string
  |TPair of etype * etype
  |TList of etype list
  |TFun of etype * etype;;

 let nextsym = ref (-1);;
let newvar = fun () -> nextsym := !nextsym + 1;
  TVar ("?T" ^ string_of_int (!nextsym));;

let newtypenv = ( [] : (ide * etype) list) ;;

let rec applytypenv (l:(ide * etype) list) (i:ide) = match l with
  | [] -> failwith "Errore applytypenv"
  | (a,t)::b -> if a = i then t else applytypenv b i;;

let rec bindtyp (e:(ide*etype)list) (i:ide) (t:etype) = match e with
    (ii , tt) :: tl when ii = i -> (i,t)::tl
  | (ii , tt) :: tl -> (ii,tt):: bindtyp tl i t
  | [] -> [(i,t)];;

(*Funzione per la creazione dei vincoli*)
let rec tconstraints (e:exp) (tr:(ide*etype)list) = match e with

    Val x ->  (applytypenv (tr) (x),[])
            
  | Eint n -> (TInt, [])
  | Echar c-> (TChar, [])
  | Ebigint b -> (TBigint,[])
  | True -> (TBool,[])
  | False -> (TBool,[])
  | Toint n -> let (t1,c1) = tconstraints n tr in (TInt, c1)
  | Tobigint n ->  let (t1,c1) = tconstraints n tr in (TBigint, c1)
                
  | Sum (e1,e2) | Diff (e1,e2) | Times (e1,e2)-> (* Sum, Diff, Times*)
      let (t1,c1) = tconstraints e1 tr in
      let (t2,c2) = tconstraints e2 tr in
      (TInt, [(t1,TInt); (t2,TInt)] @ c1 @ c2)
      
  | Bigsum (e1,e2) | Bigdiff (e1,e2) | Bigtimes (e1,e2) -> (* Bigsum, Bigdiff, Bigtimes *)
      let (t1,c1) = tconstraints e1 tr in
      let (t2,c2) = tconstraints e2 tr in
      (TBigint, [(t1,TBigint); (t2,TBigint)] @ c1 @ c2)
      
  | Less (e1,e2) -> (* Less *)
      let (t1,c1) = tconstraints e1 tr in
      let (t2,c2) = tconstraints e2 tr in
      (TBool,  [(t1,TInt); (t2,TInt)] @ c1 @ c2)
      
  | Bigless (e1,e2) -> (* Bigless *)
      let (t1,c1) = tconstraints e1 tr in
      let (t2,c2) = tconstraints e2 tr in
      (TBool, [(t1,TBigint); (t2,TBigint)] @ c1 @ c2)

  | Charless (e1,e2) -> (* Charless *)
      let (t1,c1) = tconstraints e1 tr in
      let (t2,c2) = tconstraints e2 tr in
      (TBool, [(t1,TChar); (t2,TChar)] @ c1 @ c2)
      
 | Eq (e1,e2) -> (* Equals *)
    let (t1,c1) = tconstraints e1 tr in
    let (t2,c2) = tconstraints e2 tr in
    (TBool, [(t1,t2)] @ c1 @ c2  )
    
  | Not e1 ->   (* Not *)
      let (t1,c1) = tconstraints e1 tr in
      (TBool, [(t1,TBool)] @ c1)
      
  | And (e1,e2) | Or (e1,e2) -> (* AND - OR*)
      let (t1,c1) = tconstraints e1 tr in
      let (t2,c2) = tconstraints e2 tr in
      (TBool, [(t1,TBool); (t2,TBool)] @ c1 @ c2)
      
  | Ifthenelse(e0,e1,e2) ->  (* Ifthenelse *)
      let (t0,c0) = tconstraints e0 tr in
      let (t1,c1) = tconstraints e1 tr in
      let (t2,c2) = tconstraints e2 tr in
      (t1, [(t0,TBool); (t1,t2)] @ c0 @ c1 @ c2)

  | Empty ->  (* Empty *)
     let tx = newvar() in
     (TList([tx]),[])
            
  | Cons (e1,e2) ->   (* Cons *)
      let (t1,c1) = tconstraints e1 tr in
      let (t2,c2) = tconstraints e2 tr in
      (TList([t1]), [(t2,TList([t1]))] @ c1 @ c2)
             
  | Let (x,e1,e2) -> (* Let *)
      let tx = newvar() in
      let (t1,c1) = tconstraints e1 tr in
      let (t2,c2) = tconstraints e2 (bindtyp tr x t1 ) in
      (t2,[(t1,tx)] @ c1 @ c2)
      
  | Rec (x,e1) ->  (* Rec *)
      let tx = newvar() in
      let (t1,c1) = tconstraints e1 (bindtyp tr x tx) in
      let (t2,c2) = tconstraints e1 (bindtyp tr x t1) in
      (t2, [(tx,t1)] @ c1 @ c2)
      
  | Fun (x,e1) ->  (* Fun *)
      let tx = newvar() in
      let (t1,c1) = tconstraints e1 (bindtyp tr x tx) in
      (TFun (tx,t1), c1)
      
  | Appl (e1,e2) -> (* Appl *)
      let tx = newvar() in
      let (t1,c1) = tconstraints e1 tr in
      let (t2,c2) = tconstraints e2 tr in
      (tx, [(t1,TFun(t2,tx))] @ c1 @ c2)
      
  | Epair (e1,e2) -> 
      let (t1,c1) = tconstraints e1 tr in
      let (t2,c2) = tconstraints e2 tr in
      ((TPair(t1,t2)), [(t1,t2)] @ c1 @ c2)
      
  | Head (lis) ->  (* Head *) 
     let (t1,c1) = tconstraints lis tr in
     (match t1 with
       TList([l0]) -> (l0,(c1))
      |TVar n -> (TVar n, c1)
     |_ -> failwith "Error head")
  
  | Tail (lis) ->  (* Tail *)  
    let (t1,c1) = tconstraints lis tr in 
    (match t1 with
       TList([l0]) -> (t1,(c1))
      |TVar n -> (TVar n,[t1,TList([TVar n])] @ c1)
      |_ -> failwith "Error Tail")
  
  | Fst(e)->   (* Fst *)
    let tx = newvar() in
    let (t1,c1) = tconstraints e tr in 
    (match t1 with
       TPair(e1,e2) -> 
       (e1,([e1,e1]@c1) )
      |TVar n -> (tx, [t1,TPair(tx,newvar())]@c1)
      |_ -> failwith "Error First"
      )
      
  | Snd(e) ->   (* Snd *)
  let tx = newvar() in
    let (t1,c1) = tconstraints e tr in 
    (match t1 with
       TPair(e1,e2) -> 
       (e2,([e2,e2]@c1) )
      |TVar n -> (tx, [t1,TPair(newvar(),tx)]@c1)
      |_ -> failwith "Error Second"
      )
       
 ;;     
      
let rec applysubst1 t0 x t = match t0 with  (* Not *)
    TInt -> TInt
  | TBool -> TBool
  | TBigint -> TBigint
  | TChar -> TChar
  | TVar y -> if y=x then t else TVar y
  | TFun (t1,t2) -> TFun (applysubst1 t1 x t, applysubst1 t2 x t)
  | TPair (t1,t2) -> TPair (applysubst1 t1 x t, applysubst1 t2 x t) (*non affidabili*)
  | TList (l) -> TList(listSubst l x t)
  and 

listSubst l x t= match l with
   [] -> []
      |lmn::tl -> applysubst1 lmn x t ::  listSubst tl x t
  ;;
 
let rec applysubst l x t = match l with
    [] -> []
  | (t1,t2)::l' -> (applysubst1 t1 x t, applysubst1 t2 x t)::(applysubst l' x t)
;;
 
 (*occurs indica se un identificatore di tipo è presente nel tipo*)

let rec occurs a q = match q with
  TInt
| TBool
| TBigint 
| TChar -> false (*se non incontra variabili restituisce falso*)
| TVar y -> a=y (*se le variabili sono uguali*)
| TFun (t1,t2) -> (occurs a t1) || (occurs a t2) (*continua la ricerca ricorsivamente*)
| TPair (t1,t2) -> (occurs a t1) || (occurs a t2)(*non affidabili*)
| TList (l) -> match l with 
  |TInt::tl
  |TChar::tl
  |TBigint::tl
  |TBool::tl -> (occurs a (TList(tl)))
  |TVar y :: tl -> y = a || occurs a (TList(tl))
  |TFun (t1,t2) :: tl -> (occurs a t1) || (occurs a t2) || (occurs a (TList(tl)))
  |TPair (t1,t2) :: tl-> (occurs a t1) || (occurs a t2) || (occurs a (TList(tl)))
  |TList(l2) :: tl -> (occurs a (TList(tl))) || (occurs a (TList(tl)))
  |[] -> false  
;;
 
let rec unify  (l:(etype*etype) list) = match l with
  [] -> []
| (TInt,TInt)::l' -> unify l' (*Sostituzioni identiche*)
| (TBool,TBool)::l' -> unify l' (*Sostituzioni identiche*)
| (TBigint,TBigint)::l' -> unify l' (*Sostituzioni identiche*)
| (TChar,TChar)::l' -> unify l' (*Sostituzioni identiche*)
| (TList([x]),TList([y]))::l' when x = y -> unify l'

 (*se la coppia è fatta da una variabile a ed un termine q
 in cui tale variabile non occorre allora si aggiorna
 la sostituzione s ponendo che s (a) = q 
 e si applica tale sostituzione a tutte le coppie in C*)

                                         
| (TVar a, q)::l' when not(occurs a q) -> (TVar a,q)::(unify (applysubst l' a q))

| (q, TVar a)::l' when not(occurs a q) -> (TVar a,q)::(unify (applysubst l' a q))
                                          
(*se la coppia è fatta da due termini composti da costruttori
 (nel nostro caso coppie, liste e frecce)
allora si verifica che i costruttori più esterni siano uguali, 
e se lo sono si aggiungono le coppie fatte
dai componenti accoppiati secondo le regole dell’equivalenza e 
si elimina la coppia di partenza*)

| (TFun(t1,t2),TFun(t1',t2'))::l' ->
    unify ((t1,t1') :: (t2,t2') :: l') (*quelli dopo non sono affidabili*)
  
| (TPair(x1, x2),TPair(x1',x2'))::l'->
    unify((x1,x1')::(x2,x2')::l')

| (TList(x1),TList(x2))::l'-> (*qui sono andato completamente a caso*)
    let rec listhandler (l1:etype list) (l2:etype list) = match (l1,l2) with
    
    ([],[]) -> []
    | ((hd1::tl1),(hd2::tl2)) -> (hd1,hd2)::(listhandler tl1 tl2) 
    | _ -> failwith "Liste di lunghezza diversa" in
    unify( (listhandler x1 x2) @ l' )
    
| (TList([x]),_)::l' -> unify l'
| (_,TList([x]))::l' -> unify l'
                      
| _ -> failwith "Unsolvable constraints"

     
;;
let typeinf e =
  let rec resolve t s = (match s with
    [] -> t
  | (TVar x, t')::s' -> resolve (applysubst1 t x t') s'
  | _ -> failwith ("Ill-formed substitution")) in
  let (t,c) = tconstraints e newtypenv in
  resolve t (unify c);;

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

let emptyenv = function(y:ide) -> Undefined;; 
let applyenv ((x:env),(y:ide)) = x y;;
let bind ((l:ide),(e:eval),(r:env)) = ((function lu -> if lu = l then e else applyenv (r,lu)):env);;

let diff (x,y) = match (x,y) with
  | (Int(u),Int(w)) -> Int(u-w)
  | _ -> failwith ("type diff");;

let less (x,y) = match (x,y) with
 (Int(u),Int(w)) -> Bool(u<w)
| _ -> failwith ("type less");;

let mult (x,y) = match (x,y) with
 (Int(u),Int(w)) -> Int(u*w)
| _ -> failwith ("type mult");;

let et (x,y) = match (x,y) with
 (Bool(u),Bool(w)) -> Bool(u && w)
| _ -> failwith ("type et");;

let vel (x,y) = match (x,y) with
 (Bool(u),Bool(w)) -> Bool(u||w)
| _ -> failwith ("type vel");;

let non x = match x with
 Bool(y) -> Bool(not y)
| _ -> failwith ("type non");;

let eq (x,y) = match x,y with
    Int(x), Int(y) -> Bool(x=y)                 
   |Bool(x),Bool(y) -> Bool(x && y)
   |Bigint(x), Bigint(y) -> Bool(x=y)   
   |Char(x),Char(y) -> Bool(x=y)
   |List(x),List(y) -> Bool(x=y)
   |Pair(x,y), Pair(z,zz) -> Bool(x=y)
   |_ -> failwith "error equal";;

let plus (x,y) = match (x,y) with
 (Int(u),Int(w)) -> Int(u+w)
| _ -> failwith ("type plus");;

let eval_to_list x = match x with
    List(l) -> l
| _ -> failwith ("type eval_to_list");;

let isLess (x,y) = match (x,y) with
  (Int a, Int b) -> Bool(a < b)
| _ -> failwith "Type isLess";;

let first x = match x with
  Pair(a,b) -> a
| _ -> failwith "Type fisrt";;

let second x = match x with
  Pair(a,b) -> b
| _ -> failwith "Type second";;

let segno list = match list with
    []-> failwith "errore nessun segno"
  |(el1::tl1)-> if(el1 < 0) then (-1) else 1;;

let  list_to_Big_int l1 =
  let list = l1 in
  let rec f l1 num = match l1 with
    |[]-> mult_int_big_int (segno list) num
    |(el1::tl1) ->f tl1 (add_int_big_int (abs(el1)) (mult_int_big_int 10 ( num) ))
  in f l1 (big_int_of_int 0);;

let  big_int_To_List big =
  let absolute = abs_big_int big in
  let rec aux absolute =
    if (eq_big_int absolute zero_big_int) then [] else (int_of_big_int(mod_big_int absolute (big_int_of_int 10))) :: aux (div_big_int absolute (big_int_of_int 10)) in
  match List.rev (aux absolute) with
    (el1::tl1) -> if(le_big_int big zero_big_int) then el1*(-1)::tl1 else el1::tl1
     |_->[0];;

let toInt big = match big with
    Bigint(n) ->  if(ge_big_int (list_to_Big_int n) (big_int_of_int max_int)) then Int(max_int) else  Int(int_of_big_int (list_to_Big_int n))
   |_-> failwith"Non è un rappresentabile";;

let inBigInt num = match num with
    Int(n) ->
    Bigint( big_int_To_List(big_int_of_int n))
 |_-> failwith"Non è un Bigint";;;;

let sommaBig (x,y) = match x,y with
    (Bigint x,Bigint y) ->
    Bigint (big_int_To_List(add_big_int (list_to_Big_int x) (list_to_Big_int y)))
   |_-> failwith "Errore Bigsum";;

let diffBig (x,y) = match x,y with
    (Bigint x,Bigint y) ->
      Bigint(big_int_To_List(sub_big_int (list_to_Big_int x) (list_to_Big_int y)))
     |_-> failwith "Errore Bigdiff";;

let timesBig (x,y) =   match x,y with
    (Bigint x,Bigint y) ->
 Bigint(big_int_To_List(mult_big_int (list_to_Big_int x) (list_to_Big_int y)))
   |_-> failwith "Errore BigTimes";;

let big_less (x,y) = match x,y with
    (Bigint b1 ,Bigint b2) -> le_big_int ( list_to_Big_int b1) ( list_to_Big_int b1)
 |_ -> failwith "errore big_less";;

let head l = match l with
  | [] -> failwith "errore head"
  | (a::[]) -> a
  | (a::b) -> a;;

let tail l = match l with
  | [] -> []
  | (a::[]) -> []
  | (a::b) -> b;;

let equaltype (a,b) = match a,b with
  |Int(x), y -> (match y with
                      |Int(z) -> Bool(true)
                      |_ ->Bool(false))      
  |Bool(x),y -> (match y with
                      |Bool(z) -> Bool(true)
                      |_ -> Bool(false))
  |Bigint(x), y -> (match y with
                     |Bigint(z) -> Bool(true)
                     |_ -> Bool(false))
  |Char(x), y -> (match y with
                     |Char(z) -> Bool(true)
                     |_ -> Bool(false))
  |List(x),y -> (match y with
                 |List(z) -> Bool(false)
                 |_ -> Bool(false))
  |x,List(y) -> (match x with
                 |List(z) -> Bool(true)
                 |_ -> Bool(false))
  |Pair(x,xx),y -> (match y with
                 |Pair(z,zz) -> Bool(true)
                 |_ -> Bool(false))
  |Undefined,_ -> Bool(true)
  |_,Undefined -> Bool(true)

  |_ -> Bool(false);;

let inserimentoInLista (a,l) = if (List(l))=List([]) then List(a::l)
                             else( if ((equaltype (a,(head((l))))) = Bool(true)) then List(a::l)
                             else failwith "Error Cons - Type Mismatch");;

let rec sem (e:exp) (r:env) = match e with
 Val(i) -> applyenv(r,i)
| Eint(n) -> Int(n)
| Echar(c) -> Char(c)
| Ebigint(b) -> Bigint(b)
| True -> Bool(true)
| False -> Bool(false)
| Empty -> List([])
| Sum(a,b) -> plus ((sem a r), (sem b r))
| Diff(a,b) -> diff ((sem a r), (sem b r))
| Times(a,b) -> mult ((sem a r), (sem b r))
| Bigsum(a,b) -> sommaBig ((sem a r) ,(sem b r))
| Bigdiff(a,b) -> diffBig ((sem a r), (sem b r))
| Bigtimes(a,b) -> timesBig ((sem a r),(sem b r))
| And(a,b) -> et ((sem a r), (sem b r))
| Or(a,b) -> vel ((sem a r), (sem b r))
| Not(a) -> non ((sem a r))
| Toint(a) -> toInt(sem a r)
| Tobigint(a) -> inBigInt(sem a r)
| Eq (a,b) -> eq((sem a r), (sem b r))
| Less (a,b) -> isLess((sem a r), (sem b r))
| Bigless(a,b) -> Bool(big_less ((sem a r),(sem b r)))
| Charless(a,b) ->  Bool((sem a r) < (sem b r))
| Cons(a, l) -> inserimentoInLista((sem a r),(eval_to_list(sem l r)))
| Head(a) ->  head(eval_to_list(sem a r))
| Tail(a) -> List(tail(eval_to_list(sem a r)))
| Fst (a) -> first(sem a r)  
| Snd (a) -> second(sem a r)
| Epair(a,b) -> Pair((sem a r), (sem b r))
| Ifthenelse(a,b,c) -> let g = 
    sem a r in
       if g = Bool(true)
       then sem b r
       else if g = Bool(false)
       then sem c r
       else failwith ("nonboolean guard")
| Let(i,e1,e2) -> sem e2 (bind (i, sem e1 r, r))
| Fun(i,a) -> makefun(Fun(i,a), r)
| Appl(a,b) -> applyfun(sem a r, sem b r)
| Rec(f,e) -> makefunrec (f,e,r)

and makefun ((a:exp),(x:env)) = (match a with
| Fun(ii,aa) -> Closure(a,x)
| _ -> failwith ("Non-functional object"))
and applyfun ((ev1:eval),(ev2:eval)) = (match ev1 with
| Closure(Fun(ii,aa),r) -> sem aa (bind(ii,ev2,r))
| _ -> failwith ("attempt to apply a non-functional object"))
and makefunrec (i, e1, (r:env)) =
let functional (rr:env) =
bind(i, makefun(e1,rr),r) in
let rec rfix = function x -> functional rfix x
in makefun(e1,rfix);;

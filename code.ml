exception TypeError;;
open List;;
type exp =
    Const of int
  | Abs of exp
  | Variable of string
  | Plus of exp * exp
  | Sub of exp * exp
  | Mult of exp * exp
  | Div of exp * exp
  | Mod of exp * exp
  | Exp of exp * exp
  | T
  | F
  | Not of exp
  | And of exp * exp
  | Or of exp * exp
  | Impl of exp * exp
  | Equal of exp * exp
  | Gt of exp * exp
  | Lt of exp * exp
  | Goe of exp * exp
  | Loe of exp * exp
  | Lambda of string * exp
  | Function of exp*exp;;

type opcode = CONST of int
  | ABS
  | VARIABLE of string
  | PLUS
  | SUB
  | MULT
  | DIV
  | MOD
  | EXP
  | TRUE
  | FALSE
  | NOT
  | AND
  | OR
  | IMPL
  | EQUAL
  | GT
  | LT
  | GOE
  | LOE
  | CLOS of string*opcode list
  | RET
  | APP;;


type env = (string*answer) list
and answer = Aint of int|Abool of bool | Closure of env*string*(opcode list) | Vclosure of env*exp;;

let abso e = match e with Const(n) -> Aint(abs n)
|_->raise TypeError;;


let convert_to_int t = match t with
Aint n -> n
|_->raise TypeError;;

let convert_to_bool t = match t with
Abool n -> n
|_->raise TypeError;;


let imply e = match e with
(true,false) -> false
| _ -> true;;


let rec compile e = match e with
 Const n -> [CONST(n)]
|Abs n-> (compile n)@[ABS]
|Variable n -> [VARIABLE(n)]
|Plus (n1,n2) -> (compile n1)@(compile n2)@[PLUS]
|Sub (n1,n2) -> (compile n1)@(compile n2)@[SUB]
|Mult (n1,n2) -> (compile n1)@(compile n2)@[MULT]
|Div (n1,n2) -> (compile n1)@(compile n2)@[DIV]
|Mod (n1,n2) -> (compile n1)@(compile n2)@[MOD]
|Exp (n1,n2) -> (compile n1)@(compile n2)@[EXP]
|T -> [TRUE]
|F -> [FALSE]
|Not (n1) -> (compile n1)@[NOT]
|And (n1,n2) -> (compile n1)@(compile n2)@[AND]
|Or (n1,n2) -> (compile n1)@(compile n2)@[OR]
|Impl (n1,n2) -> (compile n1)@(compile n2)@[IMPL]
|Equal (n1,n2) -> (compile n1)@(compile n2)@[EQUAL]
|Gt (n1,n2) -> (compile n1)@(compile n2)@[GT]
|Lt (n1,n2) -> (compile n1)@(compile n2)@[LT]
|Goe (n1,n2) -> (compile n1)@(compile n2)@[GOE]
|Loe (n1,n2) -> (compile n1)@(compile n2)@[LOE]
|Lambda (str,expr) -> [CLOS(str,compile(expr)@[RET])]
|Function (e1,e2) -> compile(e1) @ compile(e2) @ [APP];;

let absoexe e = match e with 
Aint(n) -> Aint(abs n)
|_-> raise TypeError;;

let rec map1 lst x =
match (x,lst) with
_,[]-> raise (Failure "Not Found")
| a,((b,v)::ls)-> 
begin 
if (a=b) then v 
else (map1 ls x)
end;;



let rec execute(s,env,c,d) = match (s,env,c,d) with
(s,env,[],d) -> hd s
|(s,env,CONST(n)::c',d) -> execute(Aint(n)::s , env, c',d)
|(Aint(n1)::Aint(n2)::s,env,PLUS::c',d) -> execute(Aint ((n1) + (n2))::s , env ,c',d)
|(Aint(n1)::Aint(n2)::s,env,SUB::c',d) -> execute(Aint ((n2) - (n1))::s, env ,c',d)
|(Aint(n1)::Aint(n2)::s,env,MULT::c',d) -> execute(Aint ((n1) * (n2))::s, env,c',d)
|(Aint(n1)::Aint(n2)::s,env,DIV::c',d) -> execute(Aint ((n2) / (n1))::s,env,c',d)
|(Aint(n1)::Aint(n2)::s,env,MOD::c',d) -> execute(Aint ((n2) mod (n1))::s,env,c',d)
|(Aint(n1)::Aint(n2)::s,env,EXP::c',d) -> execute(Aint (int_of_float ( ( float_of_int(n2) ) ** ( float_of_int(n1) ) ))::s,env,c',d)
|(n::s,env,ABS::c',d) -> execute(absoexe(n)::s, env, c',d)
|(s, env, VARIABLE(n)::c',d ) -> execute((map1 env n)::s, env, c',d)
|(s, env, TRUE::c',d) -> execute(Abool true::s, env, c' ,d)
|(s, env, FALSE::c',d) -> execute(Abool false::s, env, c' ,d)
|(Abool(n)::s , env , NOT::c',d) -> execute( Abool (not (n)) ::s,env, c',d)
|(Abool(n1)::Abool(n2)::s, env, AND::c',d) -> execute(Abool ((n2) && (n1))::s, env, c',d)
|(Abool(n1)::Abool(n2)::s, env, OR::c',d) -> execute(Abool ((n2) || (n1))::s, env, c',d)
|(Abool(n1)::Abool(n2)::s, env, IMPL::c',d) -> execute(Abool (imply (n2,n1))::s, env, c',d)
|(Aint(n1)::Aint(n2)::s, env, EQUAL::c',d) -> execute(Abool (n2 = n1)::s, env, c',d)
|(Aint(n1)::Aint(n2)::s, env, GT::c',d) -> execute(Abool (n2 > n1)::s, env, c',d)
|(Aint(n1)::Aint(n2)::s, env, LT::c',d) -> execute(Abool (n2 < n1)::s, env, c',d)
|(Aint(n1)::Aint(n2)::s, env, GOE::c',d) -> execute(Abool (n2 >= n1)::s, env, c',d)
|(Aint(n1)::Aint(n2)::s, env, LOE::c',d) -> execute(Abool (n2 <= n1)::s, env, c',d)
|(s,env,CLOS(y,c)::c',d) -> execute(Closure(env,y,c)::s,env,c',d)
|(a::Closure(env,y,c)::s, env', APP::c' , d) -> execute([],(y,a)::env', c , (s,env,c')::d)
|(a::s',env',RET::c',(s,env,c)::d) -> execute(a::s,env,c,d)
|_->raise TypeError;;


let rec eval_map rho n = match n with
Const n -> Aint n
|Abs n -> abso n
|Variable n -> map1 rho n
|Plus(n1,n2) -> Aint ( convert_to_int (eval_map rho n1) + convert_to_int (eval_map rho n2) )
|Sub(n1,n2) -> Aint ( convert_to_int (eval_map rho n1) - convert_to_int (eval_map rho n2) )
|Mult(n1,n2) -> Aint ( convert_to_int (eval_map rho n1) * convert_to_int (eval_map rho n2) )
|Div(n1,n2) -> Aint ( convert_to_int (eval_map rho n1) / convert_to_int (eval_map rho n2) )
|Mod(n1,n2) -> Aint ( convert_to_int (eval_map rho n1) mod convert_to_int (eval_map rho n2) )
|Exp(n1,n2) -> Aint (int_of_float ( ( float_of_int(convert_to_int (eval_map rho n1)) ) ** ( float_of_int(convert_to_int (eval_map rho n2)) ) ))
|T -> Abool true
|F -> Abool false
|Not n -> Abool (not (convert_to_bool(eval_map rho n)))
|And (n1,n2) -> Abool   (((convert_to_bool (eval_map rho n1))) && (convert_to_bool (eval_map rho n1)))
|Or (n1,n2) -> Abool    (((convert_to_bool (eval_map rho n1))) || (convert_to_bool (eval_map rho n2)))
|Impl (n1,n2) -> Abool  (imply ((convert_to_bool ( eval_map rho n1)),convert_to_bool(eval_map rho n2)))
|Equal (n1,n2) -> Abool ((convert_to_int(eval_map rho n1)) = convert_to_int(eval_map rho n2))
|Gt (n1,n2) -> Abool    ((convert_to_int(eval_map rho n1)) > convert_to_int(eval_map rho n2))
|Lt (n1,n2) -> Abool    ((convert_to_int(eval_map rho n1)) < convert_to_int(eval_map rho n2))
|Goe (n1,n2) -> Abool   ((convert_to_int(eval_map rho n1)) >= convert_to_int(eval_map rho n2))
|Loe (n1,n2) -> Abool   ((convert_to_int(eval_map rho n1)) <= convert_to_int(eval_map rho n2))
|_->raise TypeError;;


let rec eval_closure c = 
match c with 
Vclosure(t,e) -> eval_map t e 
| Aint(n) -> Aint(n) 
| Abool(true) -> Abool(true) 
| Abool(false) -> Abool(false)
|_->raise TypeError;;

let rec krivine (c , s) = match (c,s) with
((table,Const n),s) -> Aint n
|((table,Abs n),s) -> abso n
|((table,Variable n),s) -> eval_closure(map1 table n)
|((table,Plus(n1,n2)),s) -> Aint ( convert_to_int (eval_closure(krivine((table,n1),s))) + convert_to_int (eval_closure(krivine((table,n2),s)) ))
|((table,Sub(n1,n2)),s) -> Aint ( convert_to_int (eval_closure(krivine((table,n1),s))) - convert_to_int (eval_closure(krivine((table,n2),s)) ))
|((table, Mult(n1,n2)),s) -> Aint ( convert_to_int (eval_closure(krivine((table,n1),s))) * convert_to_int (eval_closure(krivine((table,n2),s)) ))
|((table, Div(n1,n2)),s) -> Aint ( convert_to_int (eval_closure(krivine((table,n1),s))) / convert_to_int (eval_closure(krivine((table,n2),s)) ))
|((table, Mod(n1,n2)),s) -> Aint ( convert_to_int (eval_closure(krivine((table,n1),s))) mod convert_to_int (eval_closure(krivine((table,n2),s)) ))
|((table, Exp(n1,n2)),s) -> Aint (int_of_float ( ( float_of_int(convert_to_int (eval_closure(krivine((table,n1),s))) )) ** ( float_of_int(convert_to_int (eval_closure(krivine((table,n2),s))) ) )))
|((table, T),s) -> Abool true
|((table, F),s)-> Abool false
|((table, Not n),s) -> Abool (not (convert_to_bool (eval_closure(krivine((table,n),s)))))
|((table, And (n1,n2)),s) -> Abool ((convert_to_bool (eval_closure(krivine((table,n1),s)))) && (convert_to_bool (eval_closure(krivine((table,n2),s)))))
|((table, Or (n1,n2)),s) -> Abool ((convert_to_bool (eval_closure(krivine((table,n1),s)))) || (convert_to_bool (eval_closure(krivine((table,n2),s)))))
|((table, Impl (n1,n2)),s) -> Abool (imply (convert_to_bool (eval_closure( krivine((table,n1),s))),convert_to_bool (eval_closure(krivine((table,n2),s)))))
|((table, Equal (n1,n2)),s) -> Abool (convert_to_int (eval_closure(krivine((table,n1),s))) = convert_to_int (eval_closure(krivine((table,n2),s))))
|((table, Gt (n1,n2)),s) -> Abool (convert_to_int (eval_closure(krivine((table,n1),s))) > convert_to_int (eval_closure(krivine((table,n2),s))))
|((table, Lt (n1,n2)),s) -> Abool (convert_to_int (eval_closure(krivine((table,n1),s))) < convert_to_int (eval_closure(krivine((table,n2),s))))
|((table, Goe (n1,n2)),s) -> Abool (convert_to_int (eval_closure(krivine((table,n1),s))) >= convert_to_int (eval_closure(krivine((table,n2),s))))
|((table, Loe (n1,n2) ),s) -> Abool (convert_to_int (eval_closure(krivine((table,n1),s))) <= convert_to_int (eval_closure(krivine((table,n2),s))))
|((table,Lambda(str,e)),Vclosure(table',e')::s) -> krivine(([str,Vclosure(table',e')]@table,e),s)
|((table,Function(e1,e2)),s) -> krivine((table,e1),[Vclosure(table,e2)]@s)
|_->raise TypeError;;


let g=Plus(Const(2),Const(5));;
let e1 = Function(Lambda("x",Plus(Variable("x"),Const(5))),Const(2));;
let e = Function(Lambda("x",Div(Variable("x"),Const(1))),Const(3));;
let k=Const(2);;
let e2=Div(Const(8),k);;
let f=Function (Lambda("y",Const(5)),e2);;
let f1=Function (Lambda("y",Exp(Variable("y"),Const(5))),e2);;
let f2=Function (Lambda("y",Exp(Variable("y"),e1)),Const(3));;



let print_ans e=
match e with 
Aint(n)->print_int n;print_string "\n";
|Abool(b)-> 
if b then 
begin
print_string "true";
end
else print_string "false";
|_->raise TypeError;;


let a=Plus(Const(2),Const(7));;
let aa=compile a;;
let aaa=execute([],[],aa,[]);;
print_ans (aaa);;
print_ans(krivine (([],a),[]));;

let t12 =Function (Lambda ("x",Const(3)),Div (Const(1) ,Const(0)));;
print_ans(krivine (([],t12),[]));;
print_ans(execute ([],[],(compile t12) ,[]));;

(* 
print_ans (krivine(([],f2),[]));;
print_ans (krivine(([],f),[]));;
print_ans (krivine(([],f1),[]));;
print_ans (krivine(([],e),[]));;
print_ans (krivine(([],e1),[]));;


print_ans (execute([],[],(compile f2),[]));;
print_ans (execute([],[],(compile f),[]));;
print_ans (execute([],[],(compile f1),[]));;
print_ans (execute([],[],(compile e),[]));;
print_ans (execute([],[],(compile e1),[]));;
print *)


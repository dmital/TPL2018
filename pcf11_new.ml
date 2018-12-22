(*Дмитрий Талецкий, e-mail: dmitalmail@gmail.com*)

(* Ниже ДЛ означает книгу Довек, Леви *)

(* ДЛ, с. 38 *)

type term =
| Var of string
| Abs of string * term
| App of term * term
| Int of int
| Plus of term * term
| Minus of term * term
| Times of term * term
| Div of term * term
| Ifz of term * term * term
| Fix of string * term
| Let of string * term * term

(* Оснащённые значения (extended values). ДЛ, с. 59 *)

type value =
| ValInt of int
| Closure of string * term * environment
| Thunk of term * environment
and environment = (string * value) list

type bterm =
| BVar of int
| BAbs of bterm
| BApp of bterm * bterm
| BInt of int 
| BPlus of bterm * bterm
| BMinus of bterm * bterm
| BTimes of bterm * bterm
| BDiv of bterm * bterm
| BIfz of bterm * bterm * bterm
| BFix of bterm
| BLet of bterm * bterm

type bvalue =
| BValInt of int
| BClosure of bterm * benvironment
| BThunk of bterm * benvironment
and benvironment = bvalue list

exception ComputationStuck

let emptyEnv : environment = []
let bemptyEnv : benvironment = []

let extendEnv e x v = (x, v) :: e
let bextendEnv e v = v :: e
(* Когда список рассматривается как окружение, предполагается,
что его голова расположена справа *)

(* См. standard library, module List *)
let lookup = List.assoc

(* Убирает элемент из списка *)
(* val delete : 'a -> 'a list -> 'a list *)
let delete x l = List.filter ((=) x) l

(* compare: см. module Pervasives *)
(* union возвращает объединение множеств, представленных
отсортированными списками *)
(* val union : string list -> string list -> string list *)
let union = List.merge compare

(* Напишите функцию fv : term -> string list, которая возвращает
список свободных переменных (без повторений) в терме *)

let rec fv = function
	| Int n          ->  []
	| Var v          ->  [v]
	| Abs  (x,a)     ->  delete x (fv a)
	| Fix  (x,f)     ->  delete x (fv f)	
	| Plus    (a, b) ->  union (fv a) (fv b)
	| Minus   (a, b) ->  union (fv a) (fv b)
	| Times   (a, b) ->  union (fv a) (fv b)
	| Div     (a, b) ->  union (fv a) (fv b)
	| App     (a, b) ->  union (fv a) (fv b)
	| Ifz  (a, b, c) ->  union (fv a) (union (fv b) (fv c))
	| Let  (x, a, b) ->  union (fv a) (delete x (fv b))

(* Напишите функцию byValue : environment -> term -> value, которая
вычисляет значение терма в окружении согласно вызову по значению.
Правила вывода см. в ДЛ, с. 59 *)

let rec byValue e t = match t with
	| Abs (x, t') -> Closure (x, t', e)
	| Int i -> ValInt i
	| Var x          -> (match (lookup x e) with 
		| ValInt i -> ValInt i
		| Closure (x, t', e') -> Closure (x, t', e')
		| Thunk (t', e') -> byValue e' t'
		| _ -> raise ComputationStuck
	)
	| Plus  (t1, t2) -> (match (byValue e t1, byValue e t2) with
		| (ValInt i1, ValInt i2) -> ValInt (i1 + i2)
		| _ -> raise ComputationStuck
	)
	| Minus (t1, t2) -> (match (byValue e t1, byValue e t2) with
		| (ValInt i1, ValInt i2) -> ValInt (i1 - i2)
		| _ -> raise ComputationStuck
	)
	| Times  (t1, t2) -> (match (byValue e t1, byValue e t2) with
		| (ValInt i1, ValInt i2) -> ValInt (i1 * i2)
		| _ -> raise ComputationStuck
	)
	| Div  (t1, t2) -> (match (byValue e t1, byValue e t2) with
		| (ValInt i1, ValInt i2) -> ValInt (i1 / i2)
		| _ -> raise ComputationStuck
	)
	| Ifz (t1, t2, t3) -> (match (byValue e t1) with
		| (ValInt 0) -> (byValue e t2)
		| (ValInt _) -> (byValue e t3)
		| _ -> raise ComputationStuck
	)
	| App (t1, u)     -> ( match (byValue e t1) with
		| Closure (x, t', e') -> byValue (extendEnv e' x (byValue e u)) t'
		| _ -> raise ComputationStuck
	)
	| Fix (x, t)    -> byValue (extendEnv e x (Thunk (Fix (x, t), e))) t
	| Let (x, t, u) -> byValue (extendEnv e x (byValue e t)) u

(* val evalv : term -> value *)
let evalv t = byValue emptyEnv t

let rec byName e t = match t with
	| Abs (x, t') -> Closure (x, t', e)
	| Int i -> ValInt i
	| Var x          -> (match (lookup x e) with 
		| Thunk (t', e') -> byName e' t'
		| _ -> raise ComputationStuck
	)
	| Plus  (t1, t2) -> (match (byName e t1, byName e t2) with
		| (ValInt i1, ValInt i2) -> ValInt (i1 + i2)
		| _ -> raise ComputationStuck
	)
	| Minus (t1, t2) -> (match (byName e t1, byName e t2) with
		| (ValInt i1, ValInt i2) -> ValInt (i1 - i2)
		| _ -> raise ComputationStuck
	)
	| Times  (t1, t2) -> (match (byName e t1, byName e t2) with
		| (ValInt i1, ValInt i2) -> ValInt (i1 * i2)
		| _ -> raise ComputationStuck
	)
	| Div  (t1, t2) -> (match (byName e t1, byName e t2) with
		| (ValInt i1, ValInt i2) -> ValInt (i1 / i2)
		| _ -> raise ComputationStuck
	)
	| Ifz (t1, t2, t3) -> (match (byName e t1) with
		| (ValInt 0) -> (byName e t2)
		| (ValInt _) -> (byName e t3)
		| _ -> raise ComputationStuck
	)
	| App (t1, u)     -> ( match (byName e t1) with
		| Closure (x, t2, e') -> byName (extendEnv e' x (Thunk(u, e))) t2
		| _ -> raise ComputationStuck
	)
	| Fix (x, t')    -> byName (extendEnv e x (Thunk (Fix (x, t'), e))) t'
	| Let (x, t', u) -> byName (extendEnv e x (Thunk (t', e))) u

(* val evaln : term -> value *)
let evaln t = byName emptyEnv t

(* Далее приводятся функции для тестирования. Убедитесь, что
ваша функция проходит тесты. *)

(* val factTerm : term *)
let factTerm =
  Fix ("f", Abs ("n", Ifz (Var "n", Int 1,
    Times (Var "n", App (Var "f", Minus (Var "n", Int 1))))))

let fact n = evalv (App (factTerm, Int n))


(*
# fact5;;
- : value = ValInt 120
*)

let rec byBruijn e t = match t with
	| BAbs t' -> BClosure (t', e)
	| BInt i  -> BValInt i
	| BVar n          -> (match (List.nth e n) with 
		| BValInt i -> BValInt i
		| BClosure (t', e') -> BClosure (t', e')
		| BThunk (t', e') -> byBruijn e' t'
		| _ -> raise ComputationStuck
	)
	| BPlus  (t1, t2) -> (match (byBruijn e t1, byBruijn e t2) with
		| (BValInt i1, BValInt i2) -> BValInt (i1 + i2)
		| _ -> raise ComputationStuck
	)
	| BMinus (t1, t2) -> (match (byBruijn e t1, byBruijn e t2) with
		| (BValInt i1, BValInt i2) -> BValInt (i1 - i2)
		| _ -> raise ComputationStuck
	)
	| BTimes  (t1, t2) -> (match (byBruijn e t1, byBruijn e t2) with
		| (BValInt i1, BValInt i2) -> BValInt (i1 * i2)
		| _ -> raise ComputationStuck
	)
	| BDiv  (t1, t2) -> (match (byBruijn e t1, byBruijn e t2) with
		| (BValInt i1, BValInt i2) -> BValInt (i1 / i2)
		| _ -> raise ComputationStuck
	)
	| BIfz (t1, t2, t3) -> (match (byBruijn e t1) with
		| (BValInt 0) -> (byBruijn e t2)
		| (BValInt _) -> (byBruijn e t3)
		| _ -> raise ComputationStuck
	)
	| BApp (t1, u)     -> ( match (byBruijn e t1) with
		| BClosure (t', e') -> byBruijn (bextendEnv e' (byBruijn e u)) t'
		| _ -> raise ComputationStuck
	)
	| BFix t    -> byBruijn (bextendEnv e (BThunk (BFix t, e))) t
	| BLet (t, u) -> byBruijn (bextendEnv e (byBruijn e t)) u 


(*Список переменных, встреченных при обходе терма*)
type varList = string list 

let emptyVar : varList = []

let addVariable l v = v :: l

let rec varBruijn l x n  = if List.hd l = x then BVar n else varBruijn (List.tl l) x (n + 1)


(* Ищет глубину вхождения переменной для присвоения индекса *)
let findBruijn l x = varBruijn l x 0

let rec cBruijn l t = match t with
	| Var x           -> findBruijn l x
	| Int n           -> BInt n
	| Plus  (t1, t2)  -> BPlus (cBruijn l t1, cBruijn l t2)
	| Minus (t1, t2)  -> BMinus (cBruijn l t1, cBruijn l t2)
	| Times (t1, t2)  -> BTimes (cBruijn l t1, cBruijn l t2)
	| Div   (t1, t2)  -> BDiv (cBruijn l t1, cBruijn l t2)
	| App   (t1, t2)  -> BApp (cBruijn l t1, cBruijn l t2)
	| Abs   (x,  t')  -> BAbs (cBruijn (addVariable l x) t')
	| Ifz   (u, v, w) -> BIfz (cBruijn l u, cBruijn l v, cBruijn l w)
	| Let   (x, u, w) -> BLet (cBruijn l u, cBruijn (addVariable l x) w)
	| Fix   (x, t)    -> BFix (cBruijn (addVariable l x) t)
	
(* Конвертирует терм в новый тип *)
let convertBruijn t = cBruijn emptyVar t

(* Вычисляет значение сконвертированного терма *)
let evalb t = byBruijn bemptyEnv t

let bfact n = evalb (BApp (convertBruijn factTerm, BInt n))

(*
# bfact 10;;
- : bvalue = BValInt 3628800
*)

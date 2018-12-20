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

exception ComputationStuck

let emptyEnv : environment = []

let extendEnv e x v = (x, v) :: e

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

(* val evalv : term -> value *)
let evalv t = byValue emptyEnv t

(* val evaln : term -> value *)
let evaln t = byName emptyEnv t

(* Напишите представления термов из ДЛ, упражнения 3.2 и 3.3, с. 59,
и найдите их значения с помощью eval *)

let term1 = App (App(Abs ("x", Abs ("x", Var "x")), Int 2), Int 3)
(*
# evaln term1;;
- : value = ValInt 3
*)
let term2 = App (App (Abs ("x", Abs ("y", App (Abs ("x", Plus (Var "x", Var "y")), Var "x") )), Int 5), Int 4)
(*
# evalv term2;;
- : value = ValInt 9
*)
let term3 = Let ("x", Int 4, Let ("f", Abs ("y", Plus (Var "y", Var "x")), Let ("x", Int 5, App (Var "f", Int 6))))
(*
# evaln term3;;
- : value = ValInt 10
*)

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

(* Следующий раздел посвящен тестированию с помощью чисел (нумералов) Черча.
См. Пирс, с. 62 или "Лекции по функциональному программированию", с. 17 *)

(* nthApp n s z возвращает представление терма s^n z,
то есть n-кратное применение s к z *)
(* val nthApp : int -> string -> term -> term *)
let rec nthApp n s z =
if n = 0
then z
else App (Var s, nthApp (n-1) s z)

(* Переводит целое число OCaml в нумерал Черча *)
(* val intToChurch : int -> term *)
let intToChurch n = Abs ("s", Abs ("z", nthApp n "s" (Var "z")))

(* Представление нуля в виде нумерала Черча *)
let zeroChurch = Abs ("s", Abs ("z", Var "z"))

(* Терм PCF fun x -> x + 1 *)
let add1Term = Abs ("x", Plus (Var "x", Int 1))

exception WrongValue

(* Переводит целое нумерал Черча в число OCaml *)
(* val churchToInt : term -> int *)
let churchToInt n =
  match (evaln (App (App (n, add1Term), Int 0))) with
  | ValInt i -> i
  | _ -> raise WrongValue

(* Пирс, с. 63. plus = λ m. λ n. λ s. λ z. m s (n s z) *)
let plusTerm =
  Abs ("m", Abs ("n", Abs ("s", Abs ("z",
    App (App (Var "m", Var "s"), App (App (Var "n", Var "s"), Var "z"))))))

(* times = λ m. λ n. m (plus n) 0 *)
let timesTerm =
  Abs ("m", Abs ("n",
    App (App (Var "m", App (plusTerm, Var "n")), zeroChurch)))

let checkNumOp op m n =
  App (App (op, intToChurch m), intToChurch n) |> churchToInt

(*
# checkNumOp plusTerm 3 5;;
- : int = 8
# checkNumOp timesTerm 3 5;;
- : value = 15
*)


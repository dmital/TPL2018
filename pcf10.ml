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

(* Задание 10.1 *)

(* Представление комбинаторов неподвижной точки *)

(* λf.(λx.f(xx))(λx.f(xx)) *)
let x' = Abs("x", App (Var "f", App(Var "x", Var "x")))
let combX = Abs("f", App(x',x'))

(* λf.(λx.f(λy.xxy))(λx.f(λy.xxy)) *)
let y' = Abs("x", App (Var "f", Abs ("y",App (App(Var "x",Var "x"),Var "y"))))
let combY = Abs("f", App(y',y'))

let gcdTerm = Abs("f", Abs("x", Abs("y",
				Ifz (Var "x", Var "y",   					(* если x = 0, возвращаем y *)	
				Ifz (Var "y", Var "x", 						(* если y = 0, возвращаем x *)
				Ifz (Div (Var "y", Var "x"), 
					(* если x > y, возвращаем f y (x - y * (x/y)) *)
					App(App(Var "f", Var "y"), Minus (Var "x", Times (Var "y", Div (Var "x", Var "y")))),
					(* если y > x, возвращаем f x (y - x * (y/x)) *)                   
					App(App(Var "f", Var "x"), Minus (Var "y", Times (Var "x", Div (Var "y", Var "x"))))))))))					

(* Первый комбинатор с вызовом по имени *)
let gcdnx m n = evaln (App(App(App(combX, gcdTerm),Int m),Int n))

(* Работает корректно *)
(*
# gcdnx 36 78;;
- : value = ValInt 6
*)

(* Второй комбинатор с вызовом по имени *)
let gcdny m n = evaln (App(App(App(combY, gcdTerm),Int m),Int n))

(* Работает корректно *)
(*
# gcdny 36 78;;
- : value = ValInt 6
*)

(* Первый комбинатор с вызовом по значению *)
let gcdvx m n = evalv(App(App(App(combX, gcdTerm),Int m),Int n))

(* Не работает *)
(*
# gcdvx 36 78;;
Stack overflow during evaluation (looping recursion?).
*) 

(* Второй комбинатор с вызовом по значению *)
let gcdvy m n = evalv (App(App(App(combY, gcdTerm),Int m),Int n))

(* Работает корректно *)
(*
# gcdvy 36 78;;
- : value = ValInt 6
*)


(* Задание 10.2. Интерпретатор с динамической областью видимости *)

let rec byValueDynamic e t = match t with
	| Abs (x, t') -> Closure (x, t', e)
	| Int i -> ValInt i
	| Var x          -> (match (lookup x e) with 
		| ValInt i -> ValInt i
		| Closure (x, t', e') -> Closure (x, t', e')
		| Thunk (Fix(y,t'), e') -> byValueDynamic e (Fix(y,t'))
		| _ -> raise ComputationStuck
	)
	| Plus  (t1, t2) -> (match (byValueDynamic e t1, byValueDynamic e t2) with
		| (ValInt i1, ValInt i2) -> ValInt (i1 + i2)
		| _ -> raise ComputationStuck
	)
	| Minus (t1, t2) -> (match (byValueDynamic e t1, byValueDynamic e t2) with
		| (ValInt i1, ValInt i2) -> ValInt (i1 - i2)
		| _ -> raise ComputationStuck
	)
	| Times  (t1, t2) -> (match (byValueDynamic e t1, byValueDynamic e t2) with
		| (ValInt i1, ValInt i2) -> ValInt (i1 * i2)
		| _ -> raise ComputationStuck
	)
	| Div  (t1, t2) -> (match (byValueDynamic e t1, byValueDynamic e t2) with
		| (ValInt i1, ValInt i2) -> ValInt (i1 / i2)
		| _ -> raise ComputationStuck
	)
	| Ifz (t1, t2, t3) -> (match (byValueDynamic e t1) with
		| (ValInt 0) -> (byValueDynamic e t2)
		| (ValInt _) -> (byValueDynamic e t3)
		| _ -> raise ComputationStuck
	)
	| App (t1, u)     -> ( match (byValueDynamic e t1) with
		| Closure (x, t', _) -> byValueDynamic (extendEnv e x (byValueDynamic e u)) t'
		| _ -> raise ComputationStuck
	)
	| Fix (x, t)    -> byValueDynamic (extendEnv e x (Thunk (Fix (x, t), e))) t
	| Let (x, t, u) -> byValueDynamic (extendEnv e x (byValueDynamic e t)) u


(* val evald : term -> value *)
let evald t = byValueDynamic emptyEnv t 

(* Напишите представления термов из ДЛ, упражнения 3.2 и 3.3, с. 59,
и найдите их значения с помощью eval *)

let term1 = App (App (Abs ("x", Abs("x", Var "x")) , Int 2), Int 3)
let term2' = App (Abs ("x", Plus (Var "x", Var "y")), Var "x")
let term2 = App (App (Abs ("x", Abs ("y", term2')), Int 5), Int 4) 
let term3 = App (App (Abs ("x", Abs ("y", Times (Var "x", Var "y"))), Int 2), Int 7) 
let term4 = Abs ("x", Abs ("y", Plus (Var "x", Var "y")))

(*Задание 10.3. Термы со слайда 2 лекции 4 и их значения*)

(* let x = 1 in
		let f = λy.x + y in 
			let x = 2 in f 3 *)

let dterm1 = Let ("x", Int 1, Let ("f", Abs("y",Plus(Var "x", Var "y")),Let ("x", Int 2, App(Var "f", Int 3))))
(*
# evald dterm1;;
- : value = ValInt 5
# evalv dterm1;;
- : value = ValInt 4
*)

(* let f = (let x = 1 in λy.x + y) in f 3 *)

let dterm2 = Let ("f", Let ("x", Int 1, Abs("y", Plus(Var "x", Var "y"))), App(Var "f", Int 3))

(*
# evalv dterm2;;
- : value = ValInt 4
# evald dterm2;;
Exception: Not_found.
*)


(* Задание 10.4. Два терма с переименованными связанными переменными, на которых вычисляются различные значения *)

(* let x = 1 in
		let f = λy.x + y in 
			let x = 10 in f 1 *)
let dterm3 = Let("x", Int 1, Let("f", Abs("y", Plus(Var "x", Var "y")),Let("x", Int 10, App(Var "f", Int 1))))

(* let z = 1 in
		let f = λy.z + y in 
			let x = 10 in f 1 *)
let dterm4 = Let("z", Int 1, Let("f", Abs("y", Plus(Var "z", Var "y")),Let("x", Int 10, App(Var "f", Int 1))))

(*
# evald dterm3;;
- : value = ValInt 11
# evald dterm4;;
- : value = ValInt 2
# evalv dterm3;;
- : value = ValInt 2
# evalv dterm4;;
- : value = ValInt 2
*)

(* Задание 10.5. Написать рекурсивную функцию без fix и комбинаторов неподвижной точки в динамическом интерпретаторе *)

let dterm5 n = Let("f", Abs ("n", Ifz (Var "n", Int 1, Times (Var "n", App(Var "g", Minus (Var "n", Int 1))))), Let ("g", Var "f", App (Var "g", Int n)))

(*
# evald (dterm5 10);;
- : value = ValInt 3628800
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


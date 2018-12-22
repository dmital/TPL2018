(* Тип, представляющий простые типы в PCF *)
type tpcf =
| Nat
| Arr of tpcf * tpcf
(* Окружение является списоком пар (переменная, тип) *)
and environment = (string * tpcf) list

(* Преобразование типа в строку для отображения на экране *)
(* Это делать не нужно *)
let rec tstr tn = match tn with
	| Nat -> "Nat"
	(* Эвристика для более правильной постановки скобок *)
	| Arr (x,y) -> ( match (x,y) with
		| (Nat, Nat) -> (tstr x) ^ " -> " ^ (tstr y)
		| (Nat, Arr (_, _)) -> (tstr x) ^ " -> (" ^ (tstr y) ^ ")"
		| (Arr (_ , _), Nat) -> (tstr x) ^ ") -> " ^ (tstr y)
		| (Arr (_, _), Arr (_, _)) -> " (" ^ (tstr x) ^ ") -> (" ^ (tstr y) ^ ") "
	)

type term =
| Var of string
| App of term * term
| Int of int
| Plus of term * term
| Minus of term * term
| Times of term * term
| Div of term * term
| Ifz of term * term * term
(* В Abs, Fix и Let теперь добавляются типовые аннотации *)
| Abs of string * term * tpcf
| Fix of string * term * tpcf
| Let of string * term * term * tpcf

(* Если при проверке типа что-то пошло не так *)
exception TypeError

let emptyEnv : environment = []

(* Функции для работы с окружениями не меняются *)
let extendEnv e x t = (x, t) :: e

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


let rec typeCheck e t = match t with
	| Var x -> lookup x e
	| Int i -> Nat
	| Plus (t1, t2) -> (match (typeCheck e t1, typeCheck e t2) with
		| (Nat, Nat) -> Nat
		| _ -> raise TypeError
	)
	| Minus (t1, t2) -> (match (typeCheck e t1, typeCheck e t2) with
		| (Nat, Nat) -> Nat
		| _ -> raise TypeError
	)
	| Times (t1, t2) -> (match (typeCheck e t1, typeCheck e t2) with
		| (Nat, Nat) -> Nat
		| _ -> raise TypeError
	)
	| Div (t1, t2) -> (match (typeCheck e t1, typeCheck e t2) with
		| (Nat, Nat) -> Nat
		| _ -> raise TypeError
	)
	| Ifz (t1, t2, t3) -> (match (typeCheck e t1, typeCheck e t2, typeCheck e t3) with 
	(* Первый терм должен иметь тип Nat, а два другие одинаковые типы *)
		| (Nat, tp2, tp3) -> ( match (tp2 == tp3) with
			| true -> tp2
			| false -> raise TypeError
		)
	)
	| App (u, v) -> (match typeCheck e u with
	(* Проверяем "совместимость" типов у термов u и v *)
		| Arr (tp1, tp2) -> ( match typeCheck e v with 
			| tp1 -> tp2
			| _  -> raise TypeError
		)
		| _ -> raise TypeError
	)
	(* Вычисляем тип тела функции, расширив окружение*)
	| Abs (x, u, tp1) -> ( match typeCheck (extendEnv e x tp1) u with
		| tp2  -> Arr(tp1,tp2)
		| _  -> raise TypeError
	)
	(* Вычисляем тип терма u, расширив окружение *)
	| Fix (x, u, tp) -> typeCheck (extendEnv e x tp) u 
	(* Сначала проверяем, что терм u имеет такой же тип, что и заявленный тип x *)
	| Let (x, u, v, tp) -> (match typeCheck e u with 
	(* После этого вычисляем тип v, расширив окружение*)
		| tp -> typeCheck (extendEnv e x tp) v
		| _  -> raise TypeError 
	)

(* Проверка типов, выдающая ответ в формате tpcf *)
let check t = typeCheck emptyEnv t
(* Проверка типов, выдающая ответ в формате string (не обязательно) *)
let pcheck t = tstr (check t)

(* Термы ниже придуманы мной для тестирования *) 
(* term1 = λ x. λ y. x + y *)
let term1 = Abs ("x", Abs ("y", Plus (Var "x", Var "y"), Nat), Nat)
(*
# check term1;;
- : tpcf = Arr (Nat, Arr (Nat, Nat))
# pcheck term1;;
- : string = "Nat -> (Nat -> Nat)"
*)
let term2 = App (term1, Int 10)
(*
# pcheck term2;;
- : string = "Nat -> Nat"
*)
let term3 = App (term2, Int 15)
(*
# pcheck term3;;
- : string = "Nat"
*)


(* Код первых нескольких лабораторных с подробными комментариями *)
(* Только для ознакомления, более свежие версии кода выложены отдельно *)

(*Выражения записываются в виде термов*)

type term =
(* Тип данных задается рекурсивно *)
(* Каждый терм является одним из выражений ниже *)
| Var of string
(* Терм может быть переменной, имя которой имеет тип string *)
| Abs of string * term
(* Или терм может иметь вид λx.t', где x - некоторая переменная, а t' - другой терм *)
| App of term * term
(* Аппликация  t1t2, где t1 и t2 - два терма, идущие подряд. В этом случае t2 подставляется в t1*)
| Int of int
(* Какое-то натуральное число *)
| Plus of term * term
(* Сумма двух термов *)
| Minus of term * term
(* Разность двух термов *)
| Times of term * term
(* Произведение двух термов *)
| Div of term * term
(* Частное двух термов *)
| Ifz of term * term * term
(* Структура ifz t1 then t2 else t3*)
| Fix of string * term
(* Структура fix x t, где x - переменная, а t' - терм *)
| Let of string * term * term
(* Структура let x = t1 in t2, здесь x заменяется на t1 внутри терма t2 *)

(* Оснащённые значения (extended values). ДЛ, с. 59 *)

type value =
(* Значением является что-то из перечисленного ниже *)
| ValInt of int
(* Обычное число, которое имеет тип ValInt, т.к. надо показать, что это значение *)
| Closure of string * term * environment
(* Замыкание (x,t,e) *)
(* Замыкание -- это способ хранить термы вида λx.t *)
(* При этом e может "раскручиваться" дальше, то есть тут тоже есть рекурсия *)
(* Если не можете понять, как это - ничего страшного, я сам не понимаю до конца, но все работает*)
| Thunk of term * environment
(* Структура, похожая на замыкание. В основном используется для обработки fix *)
(* Чтобы понять, как использовать замыкания и thunk'и, открываем книжку Довек, Леви и берем оттуда правила вывода *)
and environment = (string * value) list
(* Окружение -- это лист пар, где каждой переменной соответствует какое-то значение*)

(* Структуры, начинающиеся на b, предназначены для хранения термов де Брауна *)
(* Единственное отличие в том, что переменные не имеют имен *)
type bterm =
| BVar of int
(* Вместо имени у каждой переменной хранится глубина вложенности*)
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
(* В любой непонятной ситуации останавливаем вычисление *)

let emptyEnv : environment = []
let bemptyEnv : benvironment = []
(* Пустые окружения, применяются в начале реботы*)

let extendEnv e x v = (x, v) :: e
let bextendEnv e v = v :: e
(* Способ расширить окружение, добавив туда новую пару (переменная, значение) *)
(* Когда список рассматривается как окружение, предполагается,
что его голова расположена справа *)

(* См. standard library, module List *)
let lookup = List.assoc
(* Эта штука ищет значение в окружении для нужной переменной*)

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
(* Тут по-другому и не напишешь. Просто берем определение свободных переменных и прогаем его *)
(* Кому интересно, в презентациях самых первых лекций оно есть *)


(* Напишите функцию byValue : environment -> term -> value, которая
вычисляет значение терма в окружении согласно вызову по значению.
Правила вывода см. в ДЛ, с. 59 *)
(* Здесь ничего изобретать не надо. Надо просто аккуратно запрогать правила с 59 страницы книжки *)
let rec byValue e t = match t with
	(* На вход функции поступает какое-то окружение и какой-то терм. Смотрим, какой вид имеет этот терм*)
	| Abs (x, t') -> Closure (x, t', e)
	(* Как только видим абстракцию, превращаем её в замыкание по правилу вывода*)
	| Int i -> ValInt i
	(* Видим число - сразу возвращаем число *)
	| Var x          -> (match (lookup x e) with
	(* Видим переменную - ищем её значение в окружении *) 
		| ValInt i -> ValInt i
		(* Видим число - возвращаем число *)
		| Closure (x, t', e') -> Closure (x, t', e')
		(* Видим замыкание - возвращаем замыкание *)
		| Thunk (t', e') -> byValue e' t'
		(* Видим thunk - запускаем передаем терм и замыкание из него в функцию *)
		(* Почему так - не знаю. но работает же, значит, все нормально *)
		| _ -> raise ComputationStuck
		(* Других вариантов быть не может, но на всякий случай дописываем исключение *)
	)
	| Plus  (t1, t2) -> (match (byValue e t1, byValue e t2) with
		(* Если видим, сумму двух термов, пытаемся посчитать их значения по отдельности *)
		| (ValInt i1, ValInt i2) -> ValInt (i1 + i2)
		(* Если значение каждого из термов - число, то возвращаем сумму этих чисел *)
		| _ -> raise ComputationStuck
		(* Если нет - то ничего сделать нельзя, пишем ошибку *)
	)
	(* С остальной арифметикой все аналогично работает *)
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
	(* Если видим конструкцию ifz, пытаемся посчитать первый терм*)
		| (ValInt 0) -> (byValue e t2)
		(* Если его значение 0, возвращаем второй терм *)
		| (ValInt _) -> (byValue e t3)
		(* Иначе возвращаем третий терм *)
		| _ -> raise ComputationStuck
	)
	(*Случай, тогда два терма t1 и u идут один за другим*)
	| App (t1, u)     -> ( match (byValue e t1) with
		| Closure (x, t', e') -> byValue (extendEnv e' x (byValue e u)) t'
		(* Проверям, является ли t1 функцией *)
		(* Если да, то внешнюю переменную этой функции надо заменить на u *)
		(* Сразу подставить мы не можем, вместо этого кидаем в замыкание пару (x, (byValue e u) *)
		(* То есть, вычисляем значение терма u и только потом заменяем его на x. В этом и суть вызова по значению*)
		| _ -> raise ComputationStuck
		(* Если t1 не функция, то ничего сделать нельзя *)
	)
	| Fix (x, t)    -> byValue (extendEnv e x (Thunk (Fix (x, t), e))) t
	(* Тут чисто по правилу из книжки пишем *)
	| Let (x, t, u) -> byValue (extendEnv e x (byValue e t)) u
	(* Тут тоже заменяем x на значение t, см. пример с App*)

(* val evalv : term -> value *)
let evalv t = byValue emptyEnv t
(* Теперь, чтобы вычислить значение терма, запускаем его вместе с пустым окружением *)


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
		(* Отличается от вызова по значению. Опять же, прогаем правило из книжки *)
		| _ -> raise ComputationStuck
	)
	| Fix (x, t')    -> byName (extendEnv e x (Thunk (Fix (x, t'), e))) t'
	| Let (x, t', u) -> byName (extendEnv e x (Thunk (t', e))) u
	(* Отличается от вызова по значению *)

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
(* Напоминает обычный вызов по значению, но имен переменных теперь нет *)
let rec byBrown e t = match t with
	| BAbs t' -> BClosure (t', e)
	| BInt i  -> BValInt i
	| BVar n          -> (match (List.nth e n) with 
		| BValInt i -> BValInt i
		| BClosure (t', e') -> BClosure (t', e')
		| BThunk (t', e') -> byBrown e' t'
		| _ -> raise ComputationStuck
	)
	| BPlus  (t1, t2) -> (match (byBrown e t1, byBrown e t2) with
		| (BValInt i1, BValInt i2) -> BValInt (i1 + i2)
		| _ -> raise ComputationStuck
	)
	| BMinus (t1, t2) -> (match (byBrown e t1, byBrown e t2) with
		| (BValInt i1, BValInt i2) -> BValInt (i1 - i2)
		| _ -> raise ComputationStuck
	)
	| BTimes  (t1, t2) -> (match (byBrown e t1, byBrown e t2) with
		| (BValInt i1, BValInt i2) -> BValInt (i1 * i2)
		| _ -> raise ComputationStuck
	)
	| BDiv  (t1, t2) -> (match (byBrown e t1, byBrown e t2) with
		| (BValInt i1, BValInt i2) -> BValInt (i1 / i2)
		| _ -> raise ComputationStuck
	)
	| BIfz (t1, t2, t3) -> (match (byBrown e t1) with
		| (BValInt 0) -> (byBrown e t2)
		| (BValInt _) -> (byBrown e t3)
		| _ -> raise ComputationStuck
	)
	| BApp (t1, u)     -> ( match (byBrown e t1) with
		| BClosure (t', e') -> byBrown (bextendEnv e' (byBrown e u)) t'
		| _ -> raise ComputationStuck
	)
	| BFix t    -> byBrown (bextendEnv e (BThunk (BFix t, e))) t
	| BLet (t, u) -> byBrown (bextendEnv e (byBrown e t)) u 


(*Список переменных, встреченных при обходе терма*)
type varList = string list 

let emptyVar : varList = []

let addVariable l v = v :: l

let rec varBrown l x n  = match (List.hd l = x) with
|  true -> (BVar n) 
|  false  -> varBrown (List.tl l) x (n + 1)

(* Ищет глубину вхождения переменной для присвоения индекса *)
let findBrown l x = varBrown l x 0

(* Конвертирует обычный терм в терм де Брауна *)
let rec cBrown l t = match t with
	| Var x           -> findBrown l x
	(* Видим переменную - хотим заменить на число. Для этого ищем глубину вложенности *)
	| Int n           -> BInt n
	(* Тут просто возвращаем число *)
	| Plus  (t1, t2)  -> BPlus (cBrown l t1, cBrown l t2)
	(* Конвертируем каждое слагаемое по отдельности *)
	(* Список встреченных переменных тащим с собой, чтобы при необходимости считать глубину вложенности *)
	| Minus (t1, t2)  -> BMinus (cBrown l t1, cBrown l t2)
	| Times (t1, t2)  -> BTimes (cBrown l t1, cBrown l t2)
	| Div   (t1, t2)  -> BDiv (cBrown l t1, cBrown l t2)
	| App   (t1, t2)  -> BApp (cBrown l t1, cBrown l t2)
	| Abs   (x,  t')  -> BAbs (cBrown (addVariable l x) t')
	(* В случае с абстракцией кидаем переменную в начало списка и смотрим тело функции *)
	| Ifz   (u, v, w) -> BIfz (cBrown l u, cBrown l v, cBrown l w)
	(* Тоже конвертируем каждый терм по отдельности *)
	| Let   (x, u, w) -> BLet (cBrown (addVariable l x) u, cBrown (addVariable l x) w)
	(* Тут написано неправильно, как сделать правильно - пока не знаю *)
	| Fix   (x, t)    -> BFix (cBrown (addVariable l x) t)
	
(* Конвертирует терм в новый тип *)
let convertBrown t = cBrown emptyVar t

(* Вычисляет значение сконвертированного терма *)
let evalb t = byBrown bemptyEnv t

let bfact n = evalb (BApp (convertBrown factTerm, BInt n))

(*
# bfact 10;;
- : bvalue = BValInt 3628800
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


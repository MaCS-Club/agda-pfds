---
author: Игорь Федоров
title: Agda Списки
date: 2023
--- 

# Модуль List 

Определим модуль и импортируем тип равенства типов ≡ (пишется как \==) вместе с удобным синтаксисом для ведения доказательств, а так же натуральные числа и их свойства

```agda
module List where

-- Импорт модулей необходимых для ведения доказательства
import Relation.Binary.PropositionalEquality as Eq
open Eq 
open Eq.≡-Reasoning

-- Импорт натуральных чисел и их свойств
open import Data.Nat
open import Data.Nat.Properties
```

# List

Индуктивно определим тип списка с помощью конструктора пустого списка и конструктора добавляющего элемент в начало списка

```agda
infixr 4 _::_

data List(A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A -- → пишется как `\to`
```

# Длина списка

Определим функцию возвращающую длину списка. Длина пустого списка равна нулю, а длина непустого списка 1 + длина его хвоста

```agda
length : {A : Set} → List A → ℕ
length [] = 0
length (_ :: xs) = 1 + (length xs) 
```

# Интерактив 

В компиляторе Agda присутствует интерактивный режим, которым можно пользоваться для проверки написанного кода

```shell 
% agda -I src/List.lagda.md 
                 _ 
   ____         | |
  / __ \        | |
 | |__| |___  __| | ___
 |  __  / _ \/ _  |/ __\     Agda Interactive
 | |  |/ /_\ \/_| / /_| \
 |_|  |\___  /____\_____/    Type :? for help.
        __/ /
        \__/

The interactive mode is no longer under active development. Use at your own risk.
Main> 1 :: 2 :: []
1 :: 2 :: []
Main> length (1 :: 2 :: [])
2
```

# HEAD и TAIL

Определим функции head и tail

- head это функция возвращающая голову списка, т.е. первый элемент списка 
- tail это функция возвращающая хвост списка, т.е. список без первого элемента 

но обе функции определены не для всех списков, а только для не пустых 

## Определение в Haskell

В Haskell, например, определение выглядит так

```haskell
head                    :: HasCallStack => [a] -> a
head (x:_)              =  x
head []                 =  errorEmptyList "head"

tail                    :: HasCallStack => [a] -> [a]
tail (_:xs)             =  xs
tail []                 =  errorEmptyList "tail"
```

т.е. в случае пустого списка обе функции выкидывают ошибки

## Определение в Haskell (через Maybe)

Есть довольно неплохой вариант вместо ошибки возвращать ответ завернутый в тип Maybe, например, в Haskell можно определить эти функции так

```haskell
safeHead                    :: [a] -> Maybe a
safeHead (x:_)              =  Just x
safeHead []                 =  Nothing

safeTail                    :: [a] -> Maybe [a]
safeTail (_:xs)             =  Just xs
safeTail []                 =  Nothing
```

## Определение в Agda 

В Agda, с помощью зависимых типов, мы просто можем не определять head и tail на пустых списках, и их нельзя будет на них вызвать

```agda 
head : {A : Set} → (a : List A) → {length a > 0} → A 
head (x :: _) = x

tail : {A : Set} → (a : List A) → {length a > 0} → List A 
tail (_ :: xs) = xs 
```
```example
ex1 = head (1 :: 2 :: []) 

ex2 = head [] -- не может найти доказательство, что length a > 0 и просит его предъявить, при компиляции будет ошибка

ex3 = tail (1 :: 2 :: []) 

ex4 = tail [] -- не может найти доказательство, что length a > 0 и просит его предъявить, при компиляции будет ошибка
```

## Ошибка компиляции 

Не смотря на то, что непосредственно в редакторе отображается не ошибка, а подсказка, что нужно предоставить доказетельство не нулевой длины, во время компиляции действительно будет ошибка

```shell
% agda src/List.lagda.md   
Checking List (/Users/igorfedorov/Github/agda-pfds/src/List.lagda.md).
Unsolved metas at the following locations:
  /Users/igorfedorov/Github/agda-pfds/src/List.lagda.md:96,7-11
  /Users/igorfedorov/Github/agda-pfds/src/List.lagda.md:103,7-11
```

# Цепочка преобразований 

Для удобства ведения доказательств можно использовать операторы 

- `a ≡⟨⟩ b` - `a` и `b` равны по определению
- `a ≡⟨ l ⟩ b` - `a` и `b` равны по утверждению `l` 
- `∎` - конец доказательства 

Написание символов:

- ∎ - `\qed` 
- ≡ - `\==` 
- ⟨ - `\<` 
- ⟩ - `\>`

## Полезные функции 

- `(f a) ≡⟨ cong f l ⟩ (f b)` - `cong` конгруэтность, если аргументы `f` равны по `l`, т.е. `a ≡⟨ l ⟩ b`, то `(f a) ≡⟨ cong f l ⟩ (f b)`
- `b ≡⟨ sym l ⟩ a` - `sym` симметричность, если `a ≡⟨ l ⟩ b`, то `b ≡⟨ sym l ⟩ a`

# Добавление в конец

Определим функцию добавления элемента в конец списка. Добавление `a` в конец пустого списка это список из состоящий из одного элемента `a`, а добавление в конец непустого списка это добавление в конец его хвоста. 

Обратите внимание, что операция добавления в конец имеет алгоритмическую сложность O(n), где n - длина списка.

```agda
append : {A : Set} → List A → A → List A 
append [] a = a :: []
append (x :: xs) a = x :: (append xs a)
```


## Длина append

Докажем с помощью индукции, что длинна списка после применения `append` увеличивается на единицу

```agda
append-length-lemma : {A : Set} → (l : List A) → (a : A) → 
                      length (append l a) ≡ 1 + (length l)
-- База
append-length-lemma {A} [] a = 
    length (append [] a) ≡⟨⟩ 
    length (a :: []) ≡⟨⟩
    1 + (length {A} []) ∎ --необходимо явно указать тип т.к. [] может не быть типа List A
-- Шаг индукции
append-length-lemma (x :: xs) a = 
    length (append (x :: xs) a) ≡⟨⟩ 
    length (x :: (append xs a)) ≡⟨⟩ 
    1 + (length (append xs a)) ≡⟨ cong suc (append-length-lemma xs a) ⟩ 
    -- Для (length (append xs a) лемма уже доказана, поэтому используем cong suc 
    1 + (1 + (length xs)) ∎ 
```

Цепочку преобразований в которой есть `≡⟨⟩` можно заменить на `refl`, но для наглядности иногда удобнее не сокращать.

# Определение конкатенации

Определим конкатенацию двух списков

```agda
infixr 5 _++_

_++_ : {A : Set} → List A → List A → List A 
[] ++ ys = ys 
(x :: xs) ++ ys = x :: (xs ++ ys)
```

## Правый ноль

Покажем, что `[]` является правым нулем относительно конкатенации

```agda 
[]-rightUnit : {A : Set} → (a : List A) → a ++ [] ≡ a 
[]-rightUnit [] = refl
[]-rightUnit (x :: xs) = 
  (x :: xs) ++ [] ≡⟨⟩ 
  x :: (xs ++ []) ≡⟨ cong (λ l → x :: l) ([]-rightUnit xs) ⟩
  x :: xs ∎
```

## Ассоциативность конкатенации

Докажем ассоциативность конкатенации

```agda
++-assoc : {A : Set} → (a b c : List A) → (a ++ b) ++ c ≡ a ++ (b ++ c)
++-assoc [] b c = 
    ([] ++ b) ++ c ≡⟨⟩ 
    b ++ c ≡⟨⟩ 
    [] ++ (b ++ c) ∎ 
++-assoc (x :: a) b c = 
    ((x :: a) ++ b) ++ c ≡⟨⟩ 
    (x :: (a ++ b)) ++ c ≡⟨⟩ 
    x :: ((a ++ b) ++ c) ≡⟨ cong (λ y → (x :: y)) (++-assoc a b c ) ⟩ 
    -- для (a ++ b) ++ c ассоциативность доказана, поэтому используем cong 
    x :: (a ++ (b ++ c)) ≡⟨⟩ 
    (x :: a) ++ (b ++ c) ∎
```

## Длина конкатенации

Докажем, что длина конкатенации двух строк равна сумме длин этих строк

```agda
length-concat-sum : {A : Set} → (a b : List A) → 
                    length (a ++ b) ≡ length a + length b 
length-concat-sum {A} [] b = 
    length ([] ++ b) ≡⟨⟩ 
    length b ≡⟨⟩ 
    0 + length b ≡⟨⟩
    length {A} [] + length b ∎
length-concat-sum (x :: xs) b = 
    length (x :: xs ++ b) ≡⟨⟩ 
    length (x :: (xs ++ b)) ≡⟨⟩
    suc (length (xs ++ b)) ≡⟨ cong suc (length-concat-sum xs b) ⟩
    suc (length xs + length b) ∎ 
```


# Определение foldLeft 

Определим левую свертку

```agda
foldLeft : {A B : Set} → List A → B → (B → A → B) → B
foldLeft [] b _ = b
foldLeft (x :: xs) b f = foldLeft xs (f b x) f
```

# Определения reverse 

Определим функцию `reverse`, т.к. существует несколько вариантов имплементации определим их все и сможем подоказывать их эквивалентность(с точки зрения возвращаемого результата)

## Через append

`reverse` можно определить, например, через `append`

```agda
reverse-by-append :  {A : Set} -> List A -> List A
reverse-by-append [] = []
reverse-by-append (x :: v) = append (reverse-by-append v) x
```

проблема этой реализации в сложности, которая будет O(n²)

## Через concat

Можно так же использовать `concat` 

```agda
reverse-by-concat : {A : Set} → List A → List A 
reverse-by-concat [] = []
reverse-by-concat (x :: xs) = (reverse-by-concat xs) ++ (x :: [])
```

сложность этой реализации так же  O(n²)

## Через аккумулятор

Более "хитрое" решение можно написать используя аккумулятор

```agda
reverse-by-acc : {A : Set} → List A → List A → List A 
reverse-by-acc acc [] = acc 
reverse-by-acc acc (x :: xs) = reverse-by-acc (x :: acc) xs

reverse : {A : Set} → List A → List A 
reverse = reverse-by-acc []
```

сложность этой реализации уже O(n), эту реализацию и будем считать каноничной

## Через foldLeft

Аналогичная реализация, но аккумулятор мы перенесем в `foldLeft`

```agda
reverse-by-foldLeft : {A : Set} → List A → List A 
reverse-by-foldLeft l = foldLeft l [] (λ b a → a :: b)
```

так же за O(n)

# Доказательство эквивалентности реализаций `reverse`

Рассмотрим несколько доказательств эквивалентности реализаций `reverse`(остальные можно подоказывать самостоятельно)

## Через foldLeft и аккумулятор в аргументе

Докажем эквивалентность `reverse` через `foldLeft` и через аккумулятор в аргументе.
Для этого представим, что мы находимся в процессе выполнения `reverse`'а и аккумулятор уже не пуст

```agda
reverses-eq-1' : {A : Set} → (acc : List A) → (a : List A) → 
                 reverse-by-acc acc a ≡ foldLeft a acc (λ b a → a :: b)
reverses-eq-1' _ [] = refl
reverses-eq-1' acc (y :: ys) = 
    reverse-by-acc  acc (y :: ys) ≡⟨⟩ 
    reverse-by-acc  (y :: acc) ys ≡⟨ reverses-eq-1' (y :: acc) ys ⟩ 
    foldLeft ys (y :: acc) (λ b a → a :: b) ∎
```

## Через foldLeft и аккумулятор в аргументе, но "честно"

Предыдущее доказетельство не совсем честное т.к. доказывает эквивалентность на определенном шаге рекурсии, 
чтобы сделать его "честным" просто подставим вместо аккумулятора пустой список

```agda 
reverses-eq-1 : {A : Set} → (a : List A) → 
                reverse-by-acc [] a ≡ reverse-by-foldLeft a
reverses-eq-1 = reverses-eq-1' []
```

## Через acc и ++ (лемма)

Для доказательства сначала представим, что мы уже находимся на каком-то шаге рекурсии и аккумулятор не пуст, и покажем, что элемент в начале списка переносится в конец

```agda
reverses-eq-2' : {A : Set} → (acc : List A) → (l : List A) → (a : A) → 
                 reverse-by-acc acc (a :: l) ≡ reverse-by-acc [] l ++ (a :: acc)
reverses-eq-2' _ [] _ = refl
reverses-eq-2' acc (x :: []) a = refl
```

## Через acc и ++ (лемма)

```agda 
reverses-eq-2' acc (x₁ :: x₂ :: xs) a =
    reverse-by-acc acc (a :: x₁ :: x₂ :: xs) ≡⟨⟩ 
    reverse-by-acc (a :: acc) (x₁ :: x₂ :: xs) ≡⟨⟩
    reverse-by-acc (x₁ :: a :: acc) (x₂ :: xs) ≡⟨⟩
    reverse-by-acc (x₁ :: a :: acc) (x₂ :: xs) ≡⟨ reverses-eq-2' (x₁ :: a :: acc) xs x₂ ⟩ 
    reverse-by-acc [] xs ++ (x₂ :: x₁ :: a :: acc) ≡⟨⟩
    reverse-by-acc [] xs ++ ((x₂ :: x₁ :: []) ++ (a :: acc)) 
      ≡⟨ sym (++-assoc (reverse-by-acc [] xs) (x₂ :: x₁ :: []) (a :: acc))⟩ 
    (reverse-by-acc [] xs ++ (x₂ :: x₁ :: [])) ++ (a :: acc) 
      ≡⟨ cong (λ x → x ++ (a :: acc)) (sym(reverses-eq-2' (x₁ :: []) xs x₂ )) ⟩
    (reverse-by-acc (x₁ :: []) (x₂ :: xs)) ++ (a :: acc) ≡⟨⟩
    (reverse-by-acc [] (x₁ :: x₂ :: xs)) ++ (a :: acc) ∎ 
```

## Через acc и ++

Теперь можем подставить вместо аккумулятора пустой список и завершить доказательство

```agda 
reverses-eq-2 : {A : Set} → (l : List A) → 
                reverse-by-acc [] l ≡ reverse-by-concat l
reverses-eq-2 [] = refl
reverses-eq-2 (x :: xs) = 
    reverse-by-acc [] (x :: xs) ≡⟨ reverses-eq-2' [] xs x ⟩
    reverse-by-acc [] xs ++ (x :: []) 
      ≡⟨ cong (λ l → l ++ (x :: [])) (reverses-eq-2 xs) ⟩
    reverse-by-concat xs ++ (x :: []) ∎
```

# Длина reverse

```agda
reverse-length : {A : Set} → (a : List A) → length (reverse a) ≡ length a
reverse-length [] = refl
reverse-length (x :: xs) = 
  length (reverse (x :: xs))  ≡⟨ cong length (reverses-eq-2' [] xs x) ⟩
  length (reverse xs ++ (x :: [])) ≡⟨ length-concat-sum (reverse xs) (x :: []) ⟩
  length (reverse xs) + length (x :: [])
    ≡⟨ cong (λ a → a + length (x :: [])) (reverse-length xs) ⟩ 
  length xs + length (x :: []) ≡⟨⟩ 
  length xs + 1 ≡⟨ +-suc (length xs) 0 ⟩ 
  1 + (length xs) + 0 ≡⟨ +-comm ( 1 + (length xs)) 0 ⟩ 
  1 + (length xs) ∎
```  

#  `reverse` инвертирует конкатенацию

```agda 
reverse-inversion : {A : Set} → (a b : List A) → 
                    reverse (a ++ b) ≡ reverse b ++ reverse a
```

## База 

```agda 
reverse-inversion [] b = 
  reverse b ≡⟨ sym ([]-rightUnit (reverse b)) ⟩ 
  reverse b ++ [] ≡⟨⟩ 
  reverse b ++ reverse-by-concat [] 
    ≡⟨ cong (λ x → reverse b ++ x) (sym(reverses-eq-2 []))⟩
  reverse b ++ reverse [] ∎
```

## Шаг 

```agda 
reverse-inversion (x :: xs) b = 
  reverse ((x :: xs) ++ b) ≡⟨⟩ 
  reverse (x :: (xs ++ b))  ≡⟨ reverses-eq-2' [] (xs ++ b) x ⟩ 
  reverse (xs ++ b) ++ (x :: []) 
    ≡⟨ cong (λ l → l ++ (x :: [])) (reverse-inversion xs b) ⟩ 
  (reverse b ++ reverse xs) ++ (x :: []) 
    ≡⟨ ++-assoc (reverse b) (reverse xs) (x :: []) ⟩ 
  reverse b ++ (reverse xs ++ (x :: [])) 
    ≡⟨ cong (λ l → reverse b ++ l)(sym (reverses-eq-2' [] xs x)) ⟩
  reverse b ++ reverse (x :: xs) ∎
```

# Инволюция `reverse` 

```agda 
reverse-involution : {A : Set} → (a : List A) → reverse (reverse a) ≡ a
reverse-involution [] = refl
reverse-involution (x :: xs) = 
  reverse (reverse (x :: xs)) ≡⟨ cong reverse (reverses-eq-2' [] xs x) ⟩
  reverse (reverse xs ++ (x :: [])) ≡⟨⟩ 
  reverse (reverse xs ++ (x :: []))  ≡⟨ reverse-inversion (reverse xs) (x :: []) ⟩
  reverse (x :: []) ++ reverse (reverse xs) ≡⟨⟩ 
  (x :: []) ++ reverse (reverse xs) 
    ≡⟨ cong (λ l → (x :: []) ++ l) (reverse-involution xs) ⟩ 
  (x :: []) ++ xs ≡⟨⟩
  x :: ([] ++ xs) ≡⟨⟩ 
  x :: xs ∎
```
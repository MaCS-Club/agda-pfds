---
author: Игорь Федоров
title: Agda Списки
# subtitle: Установка и подключение библиотек
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

## Определение в Haskell (черезе Maybe)

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

# Добавление в конец списка

Определим функцию добавления элемента в конец списка. Добавление `a` в конец пустого списка это список из состоящий из одного элемента `a`, а добавление в конец непустого списка это добавление в конец его хвоста. 

Обратите внимание, что операция добавления в конец имеет алгоритмическую сложность O(n), где n - длина списка.

```agda
append : {A : Set} → List A → A → List A 
append [] a = a :: []
append (x :: xs) a = x :: (append xs a)
```

# append и длина

Написание символов:
- ∎ - `\qed` 
- ≡ - `\==` 
- ⟨ - `\<` 
- ⟩ - `\>`

```agda
append-length-lemma : {A : Set} → (l : List A) → (a : A) → length (append l a) ≡ 1 + (length l)
append-length-lemma {A} [] a = 
    length (append [] a) ≡⟨⟩ 
    length (a :: []) ≡⟨⟩
    1 + (length {A} []) ∎ --необходимо явно указать тип т.к. [] может не быть типа List A
append-length-lemma (x :: xs) a = 
    length (append (x :: xs) a) ≡⟨⟩ 
    length (x :: (append xs a)) ≡⟨⟩ 
    1 + (length (append xs a)) ≡⟨ cong suc (append-length-lemma xs a) ⟩ 
    1 + (1 + (length xs)) ∎ 
```

# Определение конкатенации

```agda
_++_ : {A : Set} → List A → List A → List A 
[] ++ ys = ys 
(x :: xs) ++ ys = x :: (xs ++ ys)
```

# Ассоциативность конкатенации
```agda
++-assoc : {A : Set} → (a b c : List A) → (a ++ b) ++ c ≡ a ++ (b ++ c)
++-assoc [] b c = refl
++-assoc (x :: a) b c = 
    ((x :: a) ++ b) ++ c ≡⟨⟩ 
    (x :: (a ++ b)) ++ c ≡⟨⟩ 
    x :: ((a ++ b) ++ c) ≡⟨ cong (λ y → (x :: y)) (++-assoc a b c ) ⟩ 
    x :: (a ++ (b ++ c)) ∎
```

# Длина конкатенации

```agda
length-concat-sum : {A : Set} → (a b : List A) → length (a ++ b) ≡ length a + length b 
length-concat-sum [] b = refl 
length-concat-sum (x :: xs) b = 
    length (x :: xs ++ b) ≡⟨⟩ 
    length (x :: (xs ++ b)) ≡⟨⟩
    suc (length (xs ++ b)) ≡⟨ cong suc (length-concat-sum xs b) ⟩
    suc (length xs + length b) ∎ 
```


# Определение foldLeft 

```agda
foldLeft : {A B : Set} → List A → B → (B → A → B) → B
foldLeft [] b _ = b
foldLeft (x :: xs) b f = foldLeft xs (f b x) f
```

# Определения reverse 

## Первое определение (через append)

```agda
reverse-by-append :  {A : Set} -> List A -> List A
reverse-by-append [] = []
reverse-by-append (x :: v) = append (reverse-by-append v) x
```

## Второе определение (через concat) 

```agda
reverse-by-concat : {A : Set} → List A → List A 
reverse-by-concat [] = []
reverse-by-concat (x :: xs) = (reverse-by-concat xs) ++ (x :: [])
```

## Третье определение (через аккумулятор за O(n))

```agda
reverse-by-acc : {A : Set} → List A → List A → List A 
reverse-by-acc acc [] = acc 
reverse-by-acc acc (x :: xs) = reverse-by-acc (x :: acc) xs

reverse : {A : Set} → List A → List A 
reverse = reverse-by-acc []
```

## Четвертое определение (через foldLeft)

```agda
reverse-by-fl : {A : Set} → List A → List A 
reverse-by-fl l = foldLeft l [] (λ b a → a :: b)
```

## Доказательство того, что reverse с аккумулятором тоже самое, что reverse через foldLeft

```agda
reverse-by-acc-equals-foldLeft : {A : Set} → (acc : List A) → (a : List A) → reverse-by-acc acc a ≡ foldLeft a acc (λ b a → a :: b)
reverse-by-acc-equals-foldLeft _ [] = refl
reverse-by-acc-equals-foldLeft acc (y :: ys) = 
    reverse-by-acc  acc (y :: ys) ≡⟨⟩ 
    reverse-by-acc  (y :: acc) ys ≡⟨ reverse-by-acc-equals-foldLeft (y :: acc) ys ⟩ 
    foldLeft ys (y :: acc) (λ b a → a :: b) ∎
```


## Доказательство reverse-by-acc-append-lemma

```agda
reverse-by-acc-append-lemma : {A : Set} → (acc : List A) → (l : List A) → (a : A) → reverse-by-acc acc (a :: l) ≡ reverse-by-acc [] l ++ (a :: acc)
reverse-by-acc-append-lemma _ [] _ = refl
reverse-by-acc-append-lemma acc (x :: []) a = refl
reverse-by-acc-append-lemma acc (x₁ :: x₂ :: xs) a =
    reverse-by-acc acc (a :: x₁ :: x₂ :: xs) ≡⟨⟩ 
    reverse-by-acc (a :: acc) (x₁ :: x₂ :: xs) ≡⟨⟩
    reverse-by-acc (x₁ :: a :: acc) (x₂ :: xs) ≡⟨⟩
    reverse-by-acc (x₁ :: a :: acc) (x₂ :: xs) ≡⟨ reverse-by-acc-append-lemma (x₁ :: a :: acc) xs x₂ ⟩ 
    reverse-by-acc [] xs ++ (x₂ :: x₁ :: a :: acc) ≡⟨⟩
    reverse-by-acc [] xs ++ ((x₂ :: x₁ :: []) ++ (a :: acc)) ≡⟨ sym (++-assoc (reverse-by-acc [] xs) (x₂ :: x₁ :: []) (a :: acc))⟩ 
    (reverse-by-acc [] xs ++ (x₂ :: x₁ :: [])) ++ (a :: acc) ≡⟨ cong (λ x → x ++ (a :: acc)) (sym(reverse-by-acc-append-lemma (x₁ :: []) xs x₂ )) ⟩
    (reverse-by-acc (x₁ :: []) (x₂ :: xs)) ++ (a :: acc) ≡⟨⟩
    (reverse-by-acc [] (x₁ :: x₂ :: xs)) ++ (a :: acc) ∎ 
```

# Длина reverse

```agda
reverse-length-lemma : {A : Set} → (a : List A) → length (reverse a) ≡ length a
reverse-length-lemma [] = refl
reverse-length-lemma (x :: xs) = 
  length (reverse (x :: xs)) ≡⟨ cong (length) (reverse-by-acc-append-lemma [] xs x) ⟩
  length (reverse xs ++ (x :: [])) ≡⟨ length-concat-sum (reverse xs)  (x :: []) ⟩
  length (reverse xs) + length (x :: []) ≡⟨ cong (λ a → a + length (x :: [])) (reverse-length-lemma xs) ⟩ 
  length xs + length (x :: []) ≡⟨⟩ 
  length xs + 1 ≡⟨ +-suc (length xs) 0 ⟩ 
  1 + (length xs) + 0 ≡⟨ +-comm ( 1 + (length xs)) 0 ⟩ 
  1 + (length xs) ∎
```  
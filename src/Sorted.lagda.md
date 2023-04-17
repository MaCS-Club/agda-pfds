---
author: Игорь Федоров
title: Agda Списки
date: 2023
--- 

# Модуль Sorted

Определим модуль и импортируем необходимые модули

```agda
module Sorted where

-- Импорт модулей необходимых для ведения доказательства
import Relation.Binary.PropositionalEquality as Eq
open Eq 
open Eq.≡-Reasoning

-- Импорт натуральных чисел и их свойств
open import Data.Nat
open import Data.Nat.Properties

-- Импортируем нулевой уровень вселенных типов
open import Level using (0ℓ) -- \ell 

-- Импортируем булки
open import Data.Bool using (true; false)

-- Импортируем отношения
open import Relation.Nullary using (Dec; does; yes; no; _because_)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary using (Rel) 

-- Импорт нашего списка
open import List
```

# Определения отношений порядка 

Определение отношения порядка в стандартной библиотеке из модуля `Data.Nat`:

```agda-example
data _≤_ : Rel ℕ 0ℓ where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

_<_ : Rel ℕ 0ℓ
m < n = suc m ≤ n

_≥_ : Rel ℕ 0ℓ
m ≥ n = n ≤ m

_>_ : Rel ℕ 0ℓ
m > n = n < m
```

## Примеры 

```agda 
rel-ex0 : 0 ≤ 42 
rel-ex0 = z≤n 

rel-ex1 : 2 ≤ 3
rel-ex1 = s≤s (s≤s z≤n)

rel-ex2 : 3 ≥ 2
rel-ex2 = s≤s (s≤s z≤n)

rel-ex3 : 2 < 3
rel-ex3 = s≤s (s≤s (s≤s z≤n))

rel-ex4 : 1312 ≥ 2
rel-ex4 =  s≤s (s≤s z≤n) -- тут у меня auto уже не справился
```

# Отсортированный список 

Отсортированный список относительно бинарного отношения `R` можно определить как

```agda 
data Sorted {A : Set} (R : Rel A 0ℓ) : List A → Set where 
    -- Пустой список отсортирован
    [] : Sorted R [] 
    -- Список из одного элемента уже отсортирован
    [-] : ∀ {x} → Sorted R (x :: [])
    -- Список из двух и более элементов отсортирован, если оба эти элемента отсортированы
    -- и отсортирован оставшийся список вместе со вторым элементом
    _::_ : ∀ {x y xs} → R x y → Sorted R (y :: xs) → Sorted R (x ::  y :: xs)
```

## Примеры

```agda 
sorted-ex0 : Sorted (_<_) (1 :: [])
sorted-ex0 = [-]

sorted-ex1 : Sorted (_<_) (1 :: 5 :: [])
sorted-ex1 = s≤s (s≤s z≤n) :: [-]

sorted-ex2 : Sorted (_<_) (1 :: 4 :: 6 :: 8 :: [])
sorted-ex2 = s≤s (s≤s z≤n) :: (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))) :: (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) :: [-])) 

sorted-ex3 : Sorted (_>_) (10 :: 5 :: 3 :: 1 :: [])
sorted-ex3 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) :: (s≤s (s≤s (s≤s (s≤s z≤n))) :: (s≤s (s≤s z≤n) :: [-])) 
```  

Доказательства сгенерированны через `auto`, но почему-то на `ex2` и `ex3` их синтаксис пришлось подправить ручками

# Фильтр 

Для определения фильтра на списках нам потребуется передать предикат (тип `Pred`), который может быть разрешен за конечное время (`Decidable P`)

```agda 
filter : ∀ {l} {A : Set} {P : Pred A l} → Decidable P → List A → List A 
filter P? [] = []
filter P? (x :: xs) with does (P? x)
... | false = filter P? xs
... | true  = x :: filter P? xs
```


```
filter-ex0 = filter (_<? 5) (1 :: 3 :: 5 :: 7 :: []) 
```

# "Быстрая" сортировка 

```agda 
{-# TERMINATING #-}
qsort' : {A : Set} {R : Rel A 0ℓ} → Relation.Binary.Decidable R → List A → List A
qsort' _ [] = []
qsort' R? (x :: xs) = left ++ (x :: []) ++ right
  where 
    left = qsort' R? (filter (λ e → R? e x) xs)
    right = qsort' R? (filter (λ e → R? x e) xs)

qsort'-ex0 = qsort' (_<?_) (3 :: 5 :: 7 :: 2 :: 1 :: 10 :: [])
```

## Доказательство быстрой сортировки

```agda 
qsort'-is-sort : {A : Set} {R : Rel A 0ℓ} → (R? : Relation.Binary.Decidable R) → (l : List A) → Sorted R (qsort' R? l)
qsort'-is-sort = {!   !}

```
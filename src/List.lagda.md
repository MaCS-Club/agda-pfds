---
author: Игорь Федоров
title: Agda Списки
# subtitle: Установка и подключение библиотек
date: 2023
---

# Списки 

Определение модуля 

```
module List where
```

Импорт модулей необходимых для ведения доказательства
```
import Relation.Binary.PropositionalEquality as Eq
open Eq 
open Eq.≡-Reasoning 
```

Импорт натуральных чисел
```
open import Data.Nat
```

## Определение списка

* → - `\to`

```
infixr 4 _::_

data List(A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A
```

Определение длины списка

```
length : {A : Set} → List A → ℕ 
length [] = 0
length (x :: xs) = suc (length xs) 
```

Определение добавления в конец списка 

```
append : {A : Set} → List A → A → List A 
append [] a = a :: []
append (x :: xs) a = x :: (append xs a)
```

Лемма доказывающая, что добавление элемента в конец увеличивает длинну списка на единицу

TODO: расписать какого хуя так получилось

* ∎ - ‵\qed` 
* ≡ - `\==` 
* ⟨ - `\<` 
* ⟩ - `\>`

```
append-length-lemma : {A : Set} → (l : List A) → (a : A) → length (append l a) ≡ suc (length l)
append-length-lemma [] _ = refl 
append-length-lemma (x :: xs) a = 
  length (append (x :: xs) a) ≡⟨⟩ 
  length (x :: (append xs a)) ≡⟨⟩ 
  suc (length (append xs a)) ≡⟨ cong suc (append-length-lemma xs a) ⟩ 
  suc (suc (length xs)) ∎ 
```

Определение конкатенации

```
_++_ : {A : Set} → List A → List A → List A 
[] ++ ys = ys 
(x :: xs) ++ ys = x :: (xs ++ ys)
```

Ассоциативность конкатенации
```
++-assoc : {A : Set} → (a b c : List A) → (a ++ b) ++ c ≡ a ++ (b ++ c)
++-assoc [] b c = refl
++-assoc (x :: a) b c = 
    ((x :: a) ++ b) ++ c ≡⟨⟩ 
    (x :: (a ++ b)) ++ c ≡⟨⟩ 
    x :: ((a ++ b) ++ c) ≡⟨ cong (λ y → (x :: y)) (++-assoc a b c ) ⟩ 
    x :: (a ++ (b ++ c)) ∎
```


Определение foldLeft 

```
foldLeft : {A B : Set} → List A → B → (B → A → B) → B
foldLeft [] b _ = b
foldLeft (x :: xs) b f = foldLeft xs (f b x) f
```

## Определения reverse 

### Первое определение (через append)

```
reverse-by-append :  {A : Set} -> List A -> List A
reverse-by-append [] = []
reverse-by-append (x :: v) = append (reverse-by-append v) x
```

### Второе определение (через concat) 

```
reverse-by-concat : {A : Set} → List A → List A 
reverse-by-concat [] = []
reverse-by-concat (x :: xs) = (reverse-by-concat xs) ++ (x :: [])
```

### Третье определение (через аккумулятор за O(n))

```
reverse-by-acc : {A : Set} → List A → List A → List A 
reverse-by-acc acc [] = acc 
reverse-by-acc acc (x :: xs) = reverse-by-acc (x :: acc) xs

reverse : {A : Set} → List A → List A 
reverse = reverse-by-acc []
```

### Четвертое определение (через foldLeft)

```
reverse-by-fl : {A : Set} → List A → List A 
reverse-by-fl l = foldLeft l [] (λ b a → a :: b)
```

```
reverse-by-acc-equals-foldLeft : {A : Set} → (acc : List A) → (a : List A) → reverse-by-acc acc a ≡ foldLeft a acc (λ b a → a :: b)
reverse-by-acc-equals-foldLeft _ [] = refl
reverse-by-acc-equals-foldLeft acc (y :: ys) = 
    reverse-by-acc  acc (y :: ys) ≡⟨⟩ 
    reverse-by-acc  (y :: acc) ys ≡⟨ reverse-by-acc-equals-foldLeft (y :: acc) ys ⟩ 
    foldLeft ys (y :: acc) (λ b a → a :: b) ∎
```



```
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

```
length-concat-sum : {A : Set} → (a b : List A) → length (a ++ b) ≡ length a + length b 
length-concat-sum [] b = refl 
length-concat-sum (x :: xs) b = 
    length (x :: xs ++ b) ≡⟨⟩ 
    length (x :: (xs ++ b)) ≡⟨⟩
    suc (length (xs ++ b)) ≡⟨ cong suc (length-concat-sum xs b) ⟩
    suc (length xs + length b) ∎ 
```

```
+-suc : ∀ m n → (suc m + n) ≡ (m + suc n)
+-suc zero m = refl
+-suc (suc n) m = cong suc (+-suc n m)

+-rightUnit : (n : ℕ) → (n + zero) ≡ n
+-rightUnit zero = refl
+-rightUnit (suc n) = cong suc (+-rightUnit n)

+-comm : ∀ a b → a + b ≡ b + a
+-comm zero b = sym(+-rightUnit b)
+-comm (suc a) b = trans (cong suc (+-comm a b)) (+-suc b a)
```


```
reverse-length-lemma : {A : Set} → (a : List A) → length (reverse a) ≡ length a
reverse-length-lemma [] = refl
reverse-length-lemma (x :: xs) = 
  length (reverse (x :: xs)) ≡⟨ cong (length) (reverse-by-acc-append-lemma [] xs x) ⟩
  length (reverse xs ++ (x :: [])) ≡⟨ length-concat-sum (reverse xs)  (x :: []) ⟩
  length (reverse xs) + length (x :: []) ≡⟨ cong (λ a → a + length (x :: [])) (reverse-length-lemma xs) ⟩ 
  length xs + length (x :: []) ≡⟨⟩ 
  length xs + suc zero ≡⟨ sym (+-suc (length xs) (zero)) ⟩ 
  suc(length xs) + 0 ≡⟨ +-comm ( suc(length xs)) 0 ⟩ 
  suc(length xs) ∎
``` 
structure ABICoder : sig
  type 'a word
  type char
  type abi_type
  type 'a bit0
  type num1
  type ('a, 'b) sum
  type abi_value
  val decode : string -> string -> string
  val encode : string -> string -> string
end = struct

datatype num = One | Bit0 of num | Bit1 of num;

fun equal_num (Bit0 x2) (Bit1 x3) = false
  | equal_num (Bit1 x3) (Bit0 x2) = false
  | equal_num One (Bit1 x3) = false
  | equal_num (Bit1 x3) One = false
  | equal_num One (Bit0 x2) = false
  | equal_num (Bit0 x2) One = false
  | equal_num (Bit1 x3) (Bit1 y3) = equal_num x3 y3
  | equal_num (Bit0 x2) (Bit0 y2) = equal_num x2 y2
  | equal_num One One = true;

datatype int = Zero_int | Pos of num | Neg of num;

fun equal_inta (Neg k) (Neg l) = equal_num k l
  | equal_inta (Neg k) (Pos l) = false
  | equal_inta (Neg k) Zero_int = false
  | equal_inta (Pos k) (Neg l) = false
  | equal_inta (Pos k) (Pos l) = equal_num k l
  | equal_inta (Pos k) Zero_int = false
  | equal_inta Zero_int (Neg l) = false
  | equal_inta Zero_int (Pos l) = false
  | equal_inta Zero_int Zero_int = true;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = equal_inta} : int equal;

fun plus_num (Bit1 m) (Bit1 n) = Bit0 (plus_num (plus_num m n) One)
  | plus_num (Bit1 m) (Bit0 n) = Bit1 (plus_num m n)
  | plus_num (Bit1 m) One = Bit0 (plus_num m One)
  | plus_num (Bit0 m) (Bit1 n) = Bit1 (plus_num m n)
  | plus_num (Bit0 m) (Bit0 n) = Bit0 (plus_num m n)
  | plus_num (Bit0 m) One = Bit1 m
  | plus_num One (Bit1 n) = Bit0 (plus_num n One)
  | plus_num One (Bit0 n) = Bit1 n
  | plus_num One One = Bit0 One;

fun times_num (Bit1 m) (Bit1 n) =
  Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)))
  | times_num (Bit1 m) (Bit0 n) = Bit0 (times_num (Bit1 m) n)
  | times_num (Bit0 m) (Bit1 n) = Bit0 (times_num m (Bit1 n))
  | times_num (Bit0 m) (Bit0 n) = Bit0 (Bit0 (times_num m n))
  | times_num One n = n
  | times_num m One = m;

fun times_inta (Neg m) (Neg n) = Pos (times_num m n)
  | times_inta (Neg m) (Pos n) = Neg (times_num m n)
  | times_inta (Pos m) (Neg n) = Neg (times_num m n)
  | times_inta (Pos m) (Pos n) = Pos (times_num m n)
  | times_inta Zero_int l = Zero_int
  | times_inta k Zero_int = Zero_int;

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

val times_int = {times = times_inta} : int times;

val dvd_int = {times_dvd = times_int} : int dvd;

val one_inta : int = Pos One;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = one_inta} : int one;

fun uminus_int (Neg m) = Pos m
  | uminus_int (Pos m) = Neg m
  | uminus_int Zero_int = Zero_int;

fun bitM One = One
  | bitM (Bit0 n) = Bit1 (bitM n)
  | bitM (Bit1 n) = Bit1 (Bit0 n);

fun dup (Neg n) = Neg (Bit0 n)
  | dup (Pos n) = Pos (Bit0 n)
  | dup Zero_int = Zero_int;

fun plus_inta (Neg m) (Neg n) = Neg (plus_num m n)
  | plus_inta (Neg m) (Pos n) = sub n m
  | plus_inta (Pos m) (Neg n) = sub m n
  | plus_inta (Pos m) (Pos n) = Pos (plus_num m n)
  | plus_inta Zero_int l = l
  | plus_inta k Zero_int = k
and sub (Bit0 m) (Bit1 n) = minus_inta (dup (sub m n)) one_inta
  | sub (Bit1 m) (Bit0 n) = plus_inta (dup (sub m n)) one_inta
  | sub (Bit1 m) (Bit1 n) = dup (sub m n)
  | sub (Bit0 m) (Bit0 n) = dup (sub m n)
  | sub One (Bit1 n) = Neg (Bit0 n)
  | sub One (Bit0 n) = Neg (bitM n)
  | sub (Bit1 m) One = Pos (Bit0 m)
  | sub (Bit0 m) One = Pos (bitM m)
  | sub One One = Zero_int
and minus_inta (Neg m) (Neg n) = sub n m
  | minus_inta (Neg m) (Pos n) = Neg (plus_num m n)
  | minus_inta (Pos m) (Neg n) = Pos (plus_num m n)
  | minus_inta (Pos m) (Pos n) = sub m n
  | minus_inta Zero_int l = uminus_int l
  | minus_inta k Zero_int = k;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_int = {plus = plus_inta} : int plus;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_int = {zero = Zero_int} : int zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_int = {plus_semigroup_add = plus_int} : int semigroup_add;

val numeral_int =
  {one_numeral = one_int, semigroup_add_numeral = semigroup_add_int} :
  int numeral;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val power_int = {one_power = one_int, times_power = times_int} : int power;

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_int = {minus = minus_inta} : int minus;

fun less_eq_num (Bit1 m) (Bit0 n) = less_num m n
  | less_eq_num (Bit1 m) (Bit1 n) = less_eq_num m n
  | less_eq_num (Bit0 m) (Bit1 n) = less_eq_num m n
  | less_eq_num (Bit0 m) (Bit0 n) = less_eq_num m n
  | less_eq_num (Bit1 m) One = false
  | less_eq_num (Bit0 m) One = false
  | less_eq_num One n = true
and less_num (Bit1 m) (Bit0 n) = less_num m n
  | less_num (Bit1 m) (Bit1 n) = less_num m n
  | less_num (Bit0 m) (Bit1 n) = less_eq_num m n
  | less_num (Bit0 m) (Bit0 n) = less_num m n
  | less_num One (Bit1 n) = true
  | less_num One (Bit0 n) = true
  | less_num m One = false;

fun less_eq_int (Neg k) (Neg l) = less_eq_num l k
  | less_eq_int (Neg k) (Pos l) = true
  | less_eq_int (Neg k) Zero_int = true
  | less_eq_int (Pos k) (Neg l) = false
  | less_eq_int (Pos k) (Pos l) = less_eq_num k l
  | less_eq_int (Pos k) Zero_int = false
  | less_eq_int Zero_int (Neg l) = false
  | less_eq_int Zero_int (Pos l) = true
  | less_eq_int Zero_int Zero_int = true;

fun divmod_step_int l (q, r) =
  (if less_eq_int (Pos l) r
    then (plus_inta (times_inta (Pos (Bit0 One)) q) one_inta,
           minus_inta r (Pos l))
    else (times_inta (Pos (Bit0 One)) q, r));

fun divmod_int (Bit1 m) (Bit1 n) =
  (if less_num m n then (Zero_int, Pos (Bit1 m))
    else divmod_step_int (Bit1 n) (divmod_int (Bit1 m) (Bit0 (Bit1 n))))
  | divmod_int (Bit0 m) (Bit1 n) =
    (if less_eq_num m n then (Zero_int, Pos (Bit0 m))
      else divmod_step_int (Bit1 n) (divmod_int (Bit0 m) (Bit0 (Bit1 n))))
  | divmod_int (Bit1 m) (Bit0 n) =
    let
      val (q, r) = divmod_int m n;
    in
      (q, plus_inta (times_inta (Pos (Bit0 One)) r) one_inta)
    end
  | divmod_int (Bit0 m) (Bit0 n) = let
                                     val (q, r) = divmod_int m n;
                                   in
                                     (q, times_inta (Pos (Bit0 One)) r)
                                   end
  | divmod_int One (Bit1 n) = (Zero_int, Pos One)
  | divmod_int One (Bit0 n) = (Zero_int, Pos One)
  | divmod_int (Bit1 m) One = (Pos (Bit1 m), Zero_int)
  | divmod_int (Bit0 m) One = (Pos (Bit0 m), Zero_int)
  | divmod_int One One = (Pos One, Zero_int);

fun fst (x1, x2) = x1;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

fun of_bool A_ true = one (one_zero_neq_one A_)
  | of_bool A_ false = zero (zero_zero_neq_one A_);

val zero_neq_one_int =
  {one_zero_neq_one = one_int, zero_zero_neq_one = zero_int} : int zero_neq_one;

fun adjust_div (q, r) =
  plus_inta q (of_bool zero_neq_one_int (not (equal_inta r Zero_int)));

fun divide_inta (Neg m) (Neg n) = fst (divmod_int m n)
  | divide_inta (Pos m) (Neg n) = uminus_int (adjust_div (divmod_int m n))
  | divide_inta (Neg m) (Pos n) = uminus_int (adjust_div (divmod_int m n))
  | divide_inta (Pos m) (Pos n) = fst (divmod_int m n)
  | divide_inta k (Neg One) = uminus_int k
  | divide_inta k (Pos One) = k
  | divide_inta Zero_int k = Zero_int
  | divide_inta k Zero_int = Zero_int;

type 'a divide = {divide : 'a -> 'a -> 'a};
val divide = #divide : 'a divide -> 'a -> 'a -> 'a;

val divide_int = {divide = divide_inta} : int divide;

fun snd (x1, x2) = x2;

fun adjust_mod l r =
  (if equal_inta r Zero_int then Zero_int else minus_inta l r);

fun modulo_inta (Neg m) (Neg n) = uminus_int (snd (divmod_int m n))
  | modulo_inta (Pos m) (Neg n) =
    uminus_int (adjust_mod (Pos n) (snd (divmod_int m n)))
  | modulo_inta (Neg m) (Pos n) = adjust_mod (Pos n) (snd (divmod_int m n))
  | modulo_inta (Pos m) (Pos n) = snd (divmod_int m n)
  | modulo_inta k (Neg One) = Zero_int
  | modulo_inta k (Pos One) = Zero_int
  | modulo_inta Zero_int k = Zero_int
  | modulo_inta k Zero_int = k;

type 'a modulo =
  {divide_modulo : 'a divide, dvd_modulo : 'a dvd, modulo : 'a -> 'a -> 'a};
val divide_modulo = #divide_modulo : 'a modulo -> 'a divide;
val dvd_modulo = #dvd_modulo : 'a modulo -> 'a dvd;
val modulo = #modulo : 'a modulo -> 'a -> 'a -> 'a;

val modulo_int =
  {divide_modulo = divide_int, dvd_modulo = dvd_int, modulo = modulo_inta} :
  int modulo;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};
val semiring_0_semiring_no_zero_divisors = #semiring_0_semiring_no_zero_divisors
  : 'a semiring_no_zero_divisors -> 'a semiring_0;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult,
    numeral_semiring_numeral : 'a numeral,
    semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral :
  'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral :
  'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral :
  'a semiring_numeral -> 'a semiring;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 :
  'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

type 'a semiring_1_no_zero_divisors =
  {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors :
      'a semiring_no_zero_divisors};
val semiring_1_semiring_1_no_zero_divisors =
  #semiring_1_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_1;
val semiring_no_zero_divisors_semiring_1_no_zero_divisors =
  #semiring_no_zero_divisors_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_no_zero_divisors;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add :
  'a cancel_semigroup_add -> 'a semigroup_add;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add,
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add,
    minus_cancel_ab_semigroup_add : 'a minus};
val ab_semigroup_add_cancel_ab_semigroup_add =
  #ab_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a ab_semigroup_add;
val cancel_semigroup_add_cancel_ab_semigroup_add =
  #cancel_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a cancel_semigroup_add;
val minus_cancel_ab_semigroup_add = #minus_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a minus;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add,
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};
val cancel_ab_semigroup_add_cancel_comm_monoid_add =
  #cancel_ab_semigroup_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a cancel_ab_semigroup_add;
val comm_monoid_add_cancel_comm_monoid_add =
  #comm_monoid_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a comm_monoid_add;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add,
    semiring_0_semiring_0_cancel : 'a semiring_0};
val cancel_comm_monoid_add_semiring_0_cancel =
  #cancel_comm_monoid_add_semiring_0_cancel :
  'a semiring_0_cancel -> 'a cancel_comm_monoid_add;
val semiring_0_semiring_0_cancel = #semiring_0_semiring_0_cancel :
  'a semiring_0_cancel -> 'a semiring_0;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};
val semigroup_mult_ab_semigroup_mult = #semigroup_mult_ab_semigroup_mult :
  'a ab_semigroup_mult -> 'a semigroup_mult;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult,
    semiring_comm_semiring : 'a semiring};
val ab_semigroup_mult_comm_semiring = #ab_semigroup_mult_comm_semiring :
  'a comm_semiring -> 'a ab_semigroup_mult;
val semiring_comm_semiring = #semiring_comm_semiring :
  'a comm_semiring -> 'a semiring;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring,
    semiring_0_comm_semiring_0 : 'a semiring_0};
val comm_semiring_comm_semiring_0 = #comm_semiring_comm_semiring_0 :
  'a comm_semiring_0 -> 'a comm_semiring;
val semiring_0_comm_semiring_0 = #semiring_0_comm_semiring_0 :
  'a comm_semiring_0 -> 'a semiring_0;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0,
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};
val comm_semiring_0_comm_semiring_0_cancel =
  #comm_semiring_0_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a comm_semiring_0;
val semiring_0_cancel_comm_semiring_0_cancel =
  #semiring_0_cancel_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a semiring_0_cancel;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel,
    semiring_1_semiring_1_cancel : 'a semiring_1};
val semiring_0_cancel_semiring_1_cancel = #semiring_0_cancel_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_0_cancel;
val semiring_1_semiring_1_cancel = #semiring_1_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_1;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult,
    monoid_mult_comm_monoid_mult : 'a monoid_mult,
    dvd_comm_monoid_mult : 'a dvd};
val ab_semigroup_mult_comm_monoid_mult = #ab_semigroup_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a ab_semigroup_mult;
val monoid_mult_comm_monoid_mult = #monoid_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a monoid_mult;
val dvd_comm_monoid_mult = #dvd_comm_monoid_mult :
  'a comm_monoid_mult -> 'a dvd;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult,
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0,
    semiring_1_comm_semiring_1 : 'a semiring_1};
val comm_monoid_mult_comm_semiring_1 = #comm_monoid_mult_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_monoid_mult;
val comm_semiring_0_comm_semiring_1 = #comm_semiring_0_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_semiring_0;
val semiring_1_comm_semiring_1 = #semiring_1_comm_semiring_1 :
  'a comm_semiring_1 -> 'a semiring_1;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel,
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1,
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};
val comm_semiring_0_cancel_comm_semiring_1_cancel =
  #comm_semiring_0_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_0_cancel;
val comm_semiring_1_comm_semiring_1_cancel =
  #comm_semiring_1_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_1;
val semiring_1_cancel_comm_semiring_1_cancel =
  #semiring_1_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a semiring_1_cancel;

type 'a semidom =
  {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel,
    semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};
val comm_semiring_1_cancel_semidom = #comm_semiring_1_cancel_semidom :
  'a semidom -> 'a comm_semiring_1_cancel;
val semiring_1_no_zero_divisors_semidom = #semiring_1_no_zero_divisors_semidom :
  'a semidom -> 'a semiring_1_no_zero_divisors;

val ab_semigroup_add_int = {semigroup_add_ab_semigroup_add = semigroup_add_int}
  : int ab_semigroup_add;

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} :
  int monoid_add;

val comm_monoid_add_int =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int,
    monoid_add_comm_monoid_add = monoid_add_int}
  : int comm_monoid_add;

val mult_zero_int = {times_mult_zero = times_int, zero_mult_zero = zero_int} :
  int mult_zero;

val semigroup_mult_int = {times_semigroup_mult = times_int} :
  int semigroup_mult;

val semiring_int =
  {ab_semigroup_add_semiring = ab_semigroup_add_int,
    semigroup_mult_semiring = semigroup_mult_int}
  : int semiring;

val semiring_0_int =
  {comm_monoid_add_semiring_0 = comm_monoid_add_int,
    mult_zero_semiring_0 = mult_zero_int, semiring_semiring_0 = semiring_int}
  : int semiring_0;

val semiring_no_zero_divisors_int =
  {semiring_0_semiring_no_zero_divisors = semiring_0_int} :
  int semiring_no_zero_divisors;

val monoid_mult_int =
  {semigroup_mult_monoid_mult = semigroup_mult_int,
    power_monoid_mult = power_int}
  : int monoid_mult;

val semiring_numeral_int =
  {monoid_mult_semiring_numeral = monoid_mult_int,
    numeral_semiring_numeral = numeral_int,
    semiring_semiring_numeral = semiring_int}
  : int semiring_numeral;

val semiring_1_int =
  {semiring_numeral_semiring_1 = semiring_numeral_int,
    semiring_0_semiring_1 = semiring_0_int,
    zero_neq_one_semiring_1 = zero_neq_one_int}
  : int semiring_1;

val semiring_1_no_zero_divisors_int =
  {semiring_1_semiring_1_no_zero_divisors = semiring_1_int,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors =
      semiring_no_zero_divisors_int}
  : int semiring_1_no_zero_divisors;

val cancel_semigroup_add_int =
  {semigroup_add_cancel_semigroup_add = semigroup_add_int} :
  int cancel_semigroup_add;

val cancel_ab_semigroup_add_int =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int,
    minus_cancel_ab_semigroup_add = minus_int}
  : int cancel_ab_semigroup_add;

val cancel_comm_monoid_add_int =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_int,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
  : int cancel_comm_monoid_add;

val semiring_0_cancel_int =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_int,
    semiring_0_semiring_0_cancel = semiring_0_int}
  : int semiring_0_cancel;

val ab_semigroup_mult_int =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_int} :
  int ab_semigroup_mult;

val comm_semiring_int =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_int,
    semiring_comm_semiring = semiring_int}
  : int comm_semiring;

val comm_semiring_0_int =
  {comm_semiring_comm_semiring_0 = comm_semiring_int,
    semiring_0_comm_semiring_0 = semiring_0_int}
  : int comm_semiring_0;

val comm_semiring_0_cancel_int =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_int,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_int}
  : int comm_semiring_0_cancel;

val semiring_1_cancel_int =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_int,
    semiring_1_semiring_1_cancel = semiring_1_int}
  : int semiring_1_cancel;

val comm_monoid_mult_int =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_int,
    monoid_mult_comm_monoid_mult = monoid_mult_int,
    dvd_comm_monoid_mult = dvd_int}
  : int comm_monoid_mult;

val comm_semiring_1_int =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_int,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_int,
    semiring_1_comm_semiring_1 = semiring_1_int}
  : int comm_semiring_1;

val comm_semiring_1_cancel_int =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_int,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_int,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_int}
  : int comm_semiring_1_cancel;

val semidom_int =
  {comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_int,
    semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_int}
  : int semidom;

type 'a semiring_char_0 = {semiring_1_semiring_char_0 : 'a semiring_1};
val semiring_1_semiring_char_0 = #semiring_1_semiring_char_0 :
  'a semiring_char_0 -> 'a semiring_1;

val semiring_char_0_int = {semiring_1_semiring_char_0 = semiring_1_int} :
  int semiring_char_0;

type 'a semiring_modulo =
  {comm_semiring_1_cancel_semiring_modulo : 'a comm_semiring_1_cancel,
    modulo_semiring_modulo : 'a modulo};
val comm_semiring_1_cancel_semiring_modulo =
  #comm_semiring_1_cancel_semiring_modulo :
  'a semiring_modulo -> 'a comm_semiring_1_cancel;
val modulo_semiring_modulo = #modulo_semiring_modulo :
  'a semiring_modulo -> 'a modulo;

type 'a semiring_parity =
  {semiring_modulo_semiring_parity : 'a semiring_modulo};
val semiring_modulo_semiring_parity = #semiring_modulo_semiring_parity :
  'a semiring_parity -> 'a semiring_modulo;

type 'a semiring_bits = {semiring_parity_semiring_bits : 'a semiring_parity};
val semiring_parity_semiring_bits = #semiring_parity_semiring_bits :
  'a semiring_bits -> 'a semiring_parity;

val semiring_modulo_int =
  {comm_semiring_1_cancel_semiring_modulo = comm_semiring_1_cancel_int,
    modulo_semiring_modulo = modulo_int}
  : int semiring_modulo;

val semiring_parity_int =
  {semiring_modulo_semiring_parity = semiring_modulo_int} : int semiring_parity;

val semiring_bits_int = {semiring_parity_semiring_bits = semiring_parity_int} :
  int semiring_bits;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};
val semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
  #semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
  'a semiring_no_zero_divisors_cancel -> 'a semiring_no_zero_divisors;

type 'a semidom_divide =
  {divide_semidom_divide : 'a divide, semidom_semidom_divide : 'a semidom,
    semiring_no_zero_divisors_cancel_semidom_divide :
      'a semiring_no_zero_divisors_cancel};
val divide_semidom_divide = #divide_semidom_divide :
  'a semidom_divide -> 'a divide;
val semidom_semidom_divide = #semidom_semidom_divide :
  'a semidom_divide -> 'a semidom;
val semiring_no_zero_divisors_cancel_semidom_divide =
  #semiring_no_zero_divisors_cancel_semidom_divide :
  'a semidom_divide -> 'a semiring_no_zero_divisors_cancel;

val semiring_no_zero_divisors_cancel_int =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
     semiring_no_zero_divisors_int}
  : int semiring_no_zero_divisors_cancel;

val semidom_divide_int =
  {divide_semidom_divide = divide_int, semidom_semidom_divide = semidom_int,
    semiring_no_zero_divisors_cancel_semidom_divide =
      semiring_no_zero_divisors_cancel_int}
  : int semidom_divide;

type 'a algebraic_semidom =
  {semidom_divide_algebraic_semidom : 'a semidom_divide};
val semidom_divide_algebraic_semidom = #semidom_divide_algebraic_semidom :
  'a algebraic_semidom -> 'a semidom_divide;

type 'a semidom_modulo =
  {algebraic_semidom_semidom_modulo : 'a algebraic_semidom,
    semiring_modulo_semidom_modulo : 'a semiring_modulo};
val algebraic_semidom_semidom_modulo = #algebraic_semidom_semidom_modulo :
  'a semidom_modulo -> 'a algebraic_semidom;
val semiring_modulo_semidom_modulo = #semiring_modulo_semidom_modulo :
  'a semidom_modulo -> 'a semiring_modulo;

val algebraic_semidom_int =
  {semidom_divide_algebraic_semidom = semidom_divide_int} :
  int algebraic_semidom;

val semidom_modulo_int =
  {algebraic_semidom_semidom_modulo = algebraic_semidom_int,
    semiring_modulo_semidom_modulo = semiring_modulo_int}
  : int semidom_modulo;

datatype nat = Zero_nat | Suc of nat;

fun power A_ a Zero_nat = one (one_power A_)
  | power A_ a (Suc n) = times (times_power A_) a (power A_ a n);

fun push_bit_int n k = times_inta k (power power_int (Pos (Bit0 One)) n);

fun drop_bit_int n k = divide_inta k (power power_int (Pos (Bit0 One)) n);

type 'a semiring_bit_shifts =
  {semiring_bits_semiring_bit_shifts : 'a semiring_bits,
    push_bit : nat -> 'a -> 'a, drop_bit : nat -> 'a -> 'a};
val semiring_bits_semiring_bit_shifts = #semiring_bits_semiring_bit_shifts :
  'a semiring_bit_shifts -> 'a semiring_bits;
val push_bit = #push_bit : 'a semiring_bit_shifts -> nat -> 'a -> 'a;
val drop_bit = #drop_bit : 'a semiring_bit_shifts -> nat -> 'a -> 'a;

val semiring_bit_shifts_int =
  {semiring_bits_semiring_bit_shifts = semiring_bits_int,
    push_bit = push_bit_int, drop_bit = drop_bit_int}
  : int semiring_bit_shifts;

fun less_int (Neg k) (Neg l) = less_num l k
  | less_int (Neg k) (Pos l) = true
  | less_int (Neg k) Zero_int = true
  | less_int (Pos k) (Neg l) = false
  | less_int (Pos k) (Pos l) = less_num k l
  | less_int (Pos k) Zero_int = false
  | less_int Zero_int (Neg l) = false
  | less_int Zero_int (Pos l) = true
  | less_int Zero_int Zero_int = false;

fun abs_int i = (if less_int i Zero_int then uminus_int i else i);

fun plus_nata (Suc m) n = plus_nata m (Suc n)
  | plus_nata Zero_nat n = n;

val one_nata : nat = Suc Zero_nat;

fun nat_of_num (Bit1 n) = let
                            val m = nat_of_num n;
                          in
                            Suc (plus_nata m m)
                          end
  | nat_of_num (Bit0 n) = let
                            val m = nat_of_num n;
                          in
                            plus_nata m m
                          end
  | nat_of_num One = one_nata;

fun nat (Pos k) = nat_of_num k
  | nat Zero_int = Zero_nat
  | nat (Neg k) = Zero_nat;

fun euclidean_size_int x = (nat o abs_int) x;

type 'a euclidean_semiring =
  {semidom_modulo_euclidean_semiring : 'a semidom_modulo,
    euclidean_size : 'a -> nat};
val semidom_modulo_euclidean_semiring = #semidom_modulo_euclidean_semiring :
  'a euclidean_semiring -> 'a semidom_modulo;
val euclidean_size = #euclidean_size : 'a euclidean_semiring -> 'a -> nat;

val euclidean_semiring_int =
  {semidom_modulo_euclidean_semiring = semidom_modulo_int,
    euclidean_size = euclidean_size_int}
  : int euclidean_semiring;

type 'a euclidean_semiring_cancel =
  {euclidean_semiring_euclidean_semiring_cancel : 'a euclidean_semiring};
val euclidean_semiring_euclidean_semiring_cancel =
  #euclidean_semiring_euclidean_semiring_cancel :
  'a euclidean_semiring_cancel -> 'a euclidean_semiring;

val euclidean_semiring_cancel_int =
  {euclidean_semiring_euclidean_semiring_cancel = euclidean_semiring_int} :
  int euclidean_semiring_cancel;

fun division_segment_int k =
  (if less_eq_int Zero_int k then one_inta else uminus_int one_inta);

type 'a unique_euclidean_semiring =
  {euclidean_semiring_cancel_unique_euclidean_semiring :
     'a euclidean_semiring_cancel,
    division_segment : 'a -> 'a};
val euclidean_semiring_cancel_unique_euclidean_semiring =
  #euclidean_semiring_cancel_unique_euclidean_semiring :
  'a unique_euclidean_semiring -> 'a euclidean_semiring_cancel;
val division_segment = #division_segment :
  'a unique_euclidean_semiring -> 'a -> 'a;

val unique_euclidean_semiring_int =
  {euclidean_semiring_cancel_unique_euclidean_semiring =
     euclidean_semiring_cancel_int,
    division_segment = division_segment_int}
  : int unique_euclidean_semiring;

type 'a unique_euclidean_semiring_with_nat =
  {unique_euclidean_semiring_unique_euclidean_semiring_with_nat :
     'a unique_euclidean_semiring,
    semiring_char_0_unique_euclidean_semiring_with_nat : 'a semiring_char_0,
    semiring_parity_unique_euclidean_semiring_with_nat : 'a semiring_parity};
val unique_euclidean_semiring_unique_euclidean_semiring_with_nat =
  #unique_euclidean_semiring_unique_euclidean_semiring_with_nat :
  'a unique_euclidean_semiring_with_nat -> 'a unique_euclidean_semiring;
val semiring_char_0_unique_euclidean_semiring_with_nat =
  #semiring_char_0_unique_euclidean_semiring_with_nat :
  'a unique_euclidean_semiring_with_nat -> 'a semiring_char_0;
val semiring_parity_unique_euclidean_semiring_with_nat =
  #semiring_parity_unique_euclidean_semiring_with_nat :
  'a unique_euclidean_semiring_with_nat -> 'a semiring_parity;

type 'a unique_euclidean_semiring_with_bit_shifts =
  {unique_euclidean_semiring_with_nat_unique_euclidean_semiring_with_bit_shifts
     : 'a unique_euclidean_semiring_with_nat,
    semiring_bit_shifts_unique_euclidean_semiring_with_bit_shifts :
      'a semiring_bit_shifts};
val unique_euclidean_semiring_with_nat_unique_euclidean_semiring_with_bit_shifts
  = #unique_euclidean_semiring_with_nat_unique_euclidean_semiring_with_bit_shifts
  : 'a unique_euclidean_semiring_with_bit_shifts ->
      'a unique_euclidean_semiring_with_nat;
val semiring_bit_shifts_unique_euclidean_semiring_with_bit_shifts =
  #semiring_bit_shifts_unique_euclidean_semiring_with_bit_shifts :
  'a unique_euclidean_semiring_with_bit_shifts -> 'a semiring_bit_shifts;

val unique_euclidean_semiring_with_nat_int =
  {unique_euclidean_semiring_unique_euclidean_semiring_with_nat =
     unique_euclidean_semiring_int,
    semiring_char_0_unique_euclidean_semiring_with_nat = semiring_char_0_int,
    semiring_parity_unique_euclidean_semiring_with_nat = semiring_parity_int}
  : int unique_euclidean_semiring_with_nat;

val unique_euclidean_semiring_with_bit_shifts_int =
  {unique_euclidean_semiring_with_nat_unique_euclidean_semiring_with_bit_shifts
     = unique_euclidean_semiring_with_nat_int,
    semiring_bit_shifts_unique_euclidean_semiring_with_bit_shifts =
      semiring_bit_shifts_int}
  : int unique_euclidean_semiring_with_bit_shifts;

fun times_nata Zero_nat n = Zero_nat
  | times_nata (Suc m) n = plus_nata n (times_nata m n);

val times_nat = {times = times_nata} : nat times;

val dvd_nat = {times_dvd = times_nat} : nat dvd;

val one_nat = {one = one_nata} : nat one;

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nat = {zero = Zero_nat} : nat zero;

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val numeral_nat =
  {one_numeral = one_nat, semigroup_add_numeral = semigroup_add_nat} :
  nat numeral;

val power_nat = {one_power = one_nat, times_power = times_nat} : nat power;

val ab_semigroup_add_nat = {semigroup_add_ab_semigroup_add = semigroup_add_nat}
  : nat ab_semigroup_add;

val semigroup_mult_nat = {times_semigroup_mult = times_nat} :
  nat semigroup_mult;

val semiring_nat =
  {ab_semigroup_add_semiring = ab_semigroup_add_nat,
    semigroup_mult_semiring = semigroup_mult_nat}
  : nat semiring;

val mult_zero_nat = {times_mult_zero = times_nat, zero_mult_zero = zero_nat} :
  nat mult_zero;

val monoid_add_nat =
  {semigroup_add_monoid_add = semigroup_add_nat, zero_monoid_add = zero_nat} :
  nat monoid_add;

val comm_monoid_add_nat =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_nat,
    monoid_add_comm_monoid_add = monoid_add_nat}
  : nat comm_monoid_add;

val semiring_0_nat =
  {comm_monoid_add_semiring_0 = comm_monoid_add_nat,
    mult_zero_semiring_0 = mult_zero_nat, semiring_semiring_0 = semiring_nat}
  : nat semiring_0;

val monoid_mult_nat =
  {semigroup_mult_monoid_mult = semigroup_mult_nat,
    power_monoid_mult = power_nat}
  : nat monoid_mult;

val semiring_numeral_nat =
  {monoid_mult_semiring_numeral = monoid_mult_nat,
    numeral_semiring_numeral = numeral_nat,
    semiring_semiring_numeral = semiring_nat}
  : nat semiring_numeral;

val zero_neq_one_nat =
  {one_zero_neq_one = one_nat, zero_zero_neq_one = zero_nat} : nat zero_neq_one;

val semiring_1_nat =
  {semiring_numeral_semiring_1 = semiring_numeral_nat,
    semiring_0_semiring_1 = semiring_0_nat,
    zero_neq_one_semiring_1 = zero_neq_one_nat}
  : nat semiring_1;

val ab_semigroup_mult_nat =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_nat} :
  nat ab_semigroup_mult;

val comm_semiring_nat =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_nat,
    semiring_comm_semiring = semiring_nat}
  : nat comm_semiring;

val comm_semiring_0_nat =
  {comm_semiring_comm_semiring_0 = comm_semiring_nat,
    semiring_0_comm_semiring_0 = semiring_0_nat}
  : nat comm_semiring_0;

val comm_monoid_mult_nat =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_nat,
    monoid_mult_comm_monoid_mult = monoid_mult_nat,
    dvd_comm_monoid_mult = dvd_nat}
  : nat comm_monoid_mult;

val comm_semiring_1_nat =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_nat,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_nat,
    semiring_1_comm_semiring_1 = semiring_1_nat}
  : nat comm_semiring_1;

datatype rat = Frct of (int * int);

val one_rata : rat = Frct (one_inta, one_inta);

val one_rat = {one = one_rata} : rat one;

fun quotient_of (Frct x) = x;

fun gcd_int k l =
  abs_int
    (if equal_inta l Zero_int then k
      else gcd_int l (modulo_inta (abs_int k) (abs_int l)));

fun normalize p =
  (if less_int Zero_int (snd p)
    then let
           val a = gcd_int (fst p) (snd p);
         in
           (divide_inta (fst p) a, divide_inta (snd p) a)
         end
    else (if equal_inta (snd p) Zero_int then (Zero_int, one_inta)
           else let
                  val a = uminus_int (gcd_int (fst p) (snd p));
                in
                  (divide_inta (fst p) a, divide_inta (snd p) a)
                end));

fun times_rata p q = Frct let
                            val a = quotient_of p;
                            val (aa, c) = a;
                            val b = quotient_of q;
                            val (ba, d) = b;
                          in
                            normalize (times_inta aa ba, times_inta c d)
                          end;

val times_rat = {times = times_rata} : rat times;

val power_rat = {one_power = one_rat, times_power = times_rat} : rat power;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

datatype 'a itself = Type;

type 'a len0 = {len_of : 'a itself -> nat};
val len_of = #len_of : 'a len0 -> 'a itself -> nat;

datatype 'a word = Word of int;

fun uint A_ (Word x) = x;

fun equal_worda A_ k l = equal_inta (uint A_ k) (uint A_ l);

fun equal_word A_ = {equal = equal_worda A_} : 'a word equal;

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

fun equal_chara (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
  (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
  equal_bool x1 y1 andalso
    (equal_bool x2 y2 andalso
      (equal_bool x3 y3 andalso
        (equal_bool x4 y4 andalso
          (equal_bool x5 y5 andalso
            (equal_bool x6 y6 andalso
              (equal_bool x7 y7 andalso equal_bool x8 y8))))));

val equal_char = {equal = equal_chara} : char equal;

fun equal_nat Zero_nat (Suc x2) = false
  | equal_nat (Suc x2) Zero_nat = false
  | equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2
  | equal_nat Zero_nat Zero_nat = true;

datatype abi_type = Tuint of nat | Tsint of nat | Taddr | Tbool |
  Tfixed of nat * nat | Tufixed of nat * nat | Tfbytes of nat | Tfunction |
  Tfarray of abi_type * nat | Ttuple of abi_type list | Tbytes | Tstring |
  Tarray of abi_type;

fun equal_abi_type () = {equal = equal_abi_typea} : abi_type equal
and equal_abi_typea Tstring (Tarray x13) = false
  | equal_abi_typea (Tarray x13) Tstring = false
  | equal_abi_typea Tbytes (Tarray x13) = false
  | equal_abi_typea (Tarray x13) Tbytes = false
  | equal_abi_typea Tbytes Tstring = false
  | equal_abi_typea Tstring Tbytes = false
  | equal_abi_typea (Ttuple x10) (Tarray x13) = false
  | equal_abi_typea (Tarray x13) (Ttuple x10) = false
  | equal_abi_typea (Ttuple x10) Tstring = false
  | equal_abi_typea Tstring (Ttuple x10) = false
  | equal_abi_typea (Ttuple x10) Tbytes = false
  | equal_abi_typea Tbytes (Ttuple x10) = false
  | equal_abi_typea (Tfarray (x91, x92)) (Tarray x13) = false
  | equal_abi_typea (Tarray x13) (Tfarray (x91, x92)) = false
  | equal_abi_typea (Tfarray (x91, x92)) Tstring = false
  | equal_abi_typea Tstring (Tfarray (x91, x92)) = false
  | equal_abi_typea (Tfarray (x91, x92)) Tbytes = false
  | equal_abi_typea Tbytes (Tfarray (x91, x92)) = false
  | equal_abi_typea (Tfarray (x91, x92)) (Ttuple x10) = false
  | equal_abi_typea (Ttuple x10) (Tfarray (x91, x92)) = false
  | equal_abi_typea Tfunction (Tarray x13) = false
  | equal_abi_typea (Tarray x13) Tfunction = false
  | equal_abi_typea Tfunction Tstring = false
  | equal_abi_typea Tstring Tfunction = false
  | equal_abi_typea Tfunction Tbytes = false
  | equal_abi_typea Tbytes Tfunction = false
  | equal_abi_typea Tfunction (Ttuple x10) = false
  | equal_abi_typea (Ttuple x10) Tfunction = false
  | equal_abi_typea Tfunction (Tfarray (x91, x92)) = false
  | equal_abi_typea (Tfarray (x91, x92)) Tfunction = false
  | equal_abi_typea (Tfbytes x7) (Tarray x13) = false
  | equal_abi_typea (Tarray x13) (Tfbytes x7) = false
  | equal_abi_typea (Tfbytes x7) Tstring = false
  | equal_abi_typea Tstring (Tfbytes x7) = false
  | equal_abi_typea (Tfbytes x7) Tbytes = false
  | equal_abi_typea Tbytes (Tfbytes x7) = false
  | equal_abi_typea (Tfbytes x7) (Ttuple x10) = false
  | equal_abi_typea (Ttuple x10) (Tfbytes x7) = false
  | equal_abi_typea (Tfbytes x7) (Tfarray (x91, x92)) = false
  | equal_abi_typea (Tfarray (x91, x92)) (Tfbytes x7) = false
  | equal_abi_typea (Tfbytes x7) Tfunction = false
  | equal_abi_typea Tfunction (Tfbytes x7) = false
  | equal_abi_typea (Tufixed (x61, x62)) (Tarray x13) = false
  | equal_abi_typea (Tarray x13) (Tufixed (x61, x62)) = false
  | equal_abi_typea (Tufixed (x61, x62)) Tstring = false
  | equal_abi_typea Tstring (Tufixed (x61, x62)) = false
  | equal_abi_typea (Tufixed (x61, x62)) Tbytes = false
  | equal_abi_typea Tbytes (Tufixed (x61, x62)) = false
  | equal_abi_typea (Tufixed (x61, x62)) (Ttuple x10) = false
  | equal_abi_typea (Ttuple x10) (Tufixed (x61, x62)) = false
  | equal_abi_typea (Tufixed (x61, x62)) (Tfarray (x91, x92)) = false
  | equal_abi_typea (Tfarray (x91, x92)) (Tufixed (x61, x62)) = false
  | equal_abi_typea (Tufixed (x61, x62)) Tfunction = false
  | equal_abi_typea Tfunction (Tufixed (x61, x62)) = false
  | equal_abi_typea (Tufixed (x61, x62)) (Tfbytes x7) = false
  | equal_abi_typea (Tfbytes x7) (Tufixed (x61, x62)) = false
  | equal_abi_typea (Tfixed (x51, x52)) (Tarray x13) = false
  | equal_abi_typea (Tarray x13) (Tfixed (x51, x52)) = false
  | equal_abi_typea (Tfixed (x51, x52)) Tstring = false
  | equal_abi_typea Tstring (Tfixed (x51, x52)) = false
  | equal_abi_typea (Tfixed (x51, x52)) Tbytes = false
  | equal_abi_typea Tbytes (Tfixed (x51, x52)) = false
  | equal_abi_typea (Tfixed (x51, x52)) (Ttuple x10) = false
  | equal_abi_typea (Ttuple x10) (Tfixed (x51, x52)) = false
  | equal_abi_typea (Tfixed (x51, x52)) (Tfarray (x91, x92)) = false
  | equal_abi_typea (Tfarray (x91, x92)) (Tfixed (x51, x52)) = false
  | equal_abi_typea (Tfixed (x51, x52)) Tfunction = false
  | equal_abi_typea Tfunction (Tfixed (x51, x52)) = false
  | equal_abi_typea (Tfixed (x51, x52)) (Tfbytes x7) = false
  | equal_abi_typea (Tfbytes x7) (Tfixed (x51, x52)) = false
  | equal_abi_typea (Tfixed (x51, x52)) (Tufixed (x61, x62)) = false
  | equal_abi_typea (Tufixed (x61, x62)) (Tfixed (x51, x52)) = false
  | equal_abi_typea Tbool (Tarray x13) = false
  | equal_abi_typea (Tarray x13) Tbool = false
  | equal_abi_typea Tbool Tstring = false
  | equal_abi_typea Tstring Tbool = false
  | equal_abi_typea Tbool Tbytes = false
  | equal_abi_typea Tbytes Tbool = false
  | equal_abi_typea Tbool (Ttuple x10) = false
  | equal_abi_typea (Ttuple x10) Tbool = false
  | equal_abi_typea Tbool (Tfarray (x91, x92)) = false
  | equal_abi_typea (Tfarray (x91, x92)) Tbool = false
  | equal_abi_typea Tbool Tfunction = false
  | equal_abi_typea Tfunction Tbool = false
  | equal_abi_typea Tbool (Tfbytes x7) = false
  | equal_abi_typea (Tfbytes x7) Tbool = false
  | equal_abi_typea Tbool (Tufixed (x61, x62)) = false
  | equal_abi_typea (Tufixed (x61, x62)) Tbool = false
  | equal_abi_typea Tbool (Tfixed (x51, x52)) = false
  | equal_abi_typea (Tfixed (x51, x52)) Tbool = false
  | equal_abi_typea Taddr (Tarray x13) = false
  | equal_abi_typea (Tarray x13) Taddr = false
  | equal_abi_typea Taddr Tstring = false
  | equal_abi_typea Tstring Taddr = false
  | equal_abi_typea Taddr Tbytes = false
  | equal_abi_typea Tbytes Taddr = false
  | equal_abi_typea Taddr (Ttuple x10) = false
  | equal_abi_typea (Ttuple x10) Taddr = false
  | equal_abi_typea Taddr (Tfarray (x91, x92)) = false
  | equal_abi_typea (Tfarray (x91, x92)) Taddr = false
  | equal_abi_typea Taddr Tfunction = false
  | equal_abi_typea Tfunction Taddr = false
  | equal_abi_typea Taddr (Tfbytes x7) = false
  | equal_abi_typea (Tfbytes x7) Taddr = false
  | equal_abi_typea Taddr (Tufixed (x61, x62)) = false
  | equal_abi_typea (Tufixed (x61, x62)) Taddr = false
  | equal_abi_typea Taddr (Tfixed (x51, x52)) = false
  | equal_abi_typea (Tfixed (x51, x52)) Taddr = false
  | equal_abi_typea Taddr Tbool = false
  | equal_abi_typea Tbool Taddr = false
  | equal_abi_typea (Tsint x2) (Tarray x13) = false
  | equal_abi_typea (Tarray x13) (Tsint x2) = false
  | equal_abi_typea (Tsint x2) Tstring = false
  | equal_abi_typea Tstring (Tsint x2) = false
  | equal_abi_typea (Tsint x2) Tbytes = false
  | equal_abi_typea Tbytes (Tsint x2) = false
  | equal_abi_typea (Tsint x2) (Ttuple x10) = false
  | equal_abi_typea (Ttuple x10) (Tsint x2) = false
  | equal_abi_typea (Tsint x2) (Tfarray (x91, x92)) = false
  | equal_abi_typea (Tfarray (x91, x92)) (Tsint x2) = false
  | equal_abi_typea (Tsint x2) Tfunction = false
  | equal_abi_typea Tfunction (Tsint x2) = false
  | equal_abi_typea (Tsint x2) (Tfbytes x7) = false
  | equal_abi_typea (Tfbytes x7) (Tsint x2) = false
  | equal_abi_typea (Tsint x2) (Tufixed (x61, x62)) = false
  | equal_abi_typea (Tufixed (x61, x62)) (Tsint x2) = false
  | equal_abi_typea (Tsint x2) (Tfixed (x51, x52)) = false
  | equal_abi_typea (Tfixed (x51, x52)) (Tsint x2) = false
  | equal_abi_typea (Tsint x2) Tbool = false
  | equal_abi_typea Tbool (Tsint x2) = false
  | equal_abi_typea (Tsint x2) Taddr = false
  | equal_abi_typea Taddr (Tsint x2) = false
  | equal_abi_typea (Tuint x1) (Tarray x13) = false
  | equal_abi_typea (Tarray x13) (Tuint x1) = false
  | equal_abi_typea (Tuint x1) Tstring = false
  | equal_abi_typea Tstring (Tuint x1) = false
  | equal_abi_typea (Tuint x1) Tbytes = false
  | equal_abi_typea Tbytes (Tuint x1) = false
  | equal_abi_typea (Tuint x1) (Ttuple x10) = false
  | equal_abi_typea (Ttuple x10) (Tuint x1) = false
  | equal_abi_typea (Tuint x1) (Tfarray (x91, x92)) = false
  | equal_abi_typea (Tfarray (x91, x92)) (Tuint x1) = false
  | equal_abi_typea (Tuint x1) Tfunction = false
  | equal_abi_typea Tfunction (Tuint x1) = false
  | equal_abi_typea (Tuint x1) (Tfbytes x7) = false
  | equal_abi_typea (Tfbytes x7) (Tuint x1) = false
  | equal_abi_typea (Tuint x1) (Tufixed (x61, x62)) = false
  | equal_abi_typea (Tufixed (x61, x62)) (Tuint x1) = false
  | equal_abi_typea (Tuint x1) (Tfixed (x51, x52)) = false
  | equal_abi_typea (Tfixed (x51, x52)) (Tuint x1) = false
  | equal_abi_typea (Tuint x1) Tbool = false
  | equal_abi_typea Tbool (Tuint x1) = false
  | equal_abi_typea (Tuint x1) Taddr = false
  | equal_abi_typea Taddr (Tuint x1) = false
  | equal_abi_typea (Tuint x1) (Tsint x2) = false
  | equal_abi_typea (Tsint x2) (Tuint x1) = false
  | equal_abi_typea (Tarray x13) (Tarray y13) = equal_abi_typea x13 y13
  | equal_abi_typea (Ttuple x10) (Ttuple y10) =
    equal_lista (equal_abi_type ()) x10 y10
  | equal_abi_typea (Tfarray (x91, x92)) (Tfarray (y91, y92)) =
    equal_abi_typea x91 y91 andalso equal_nat x92 y92
  | equal_abi_typea (Tfbytes x7) (Tfbytes y7) = equal_nat x7 y7
  | equal_abi_typea (Tufixed (x61, x62)) (Tufixed (y61, y62)) =
    equal_nat x61 y61 andalso equal_nat x62 y62
  | equal_abi_typea (Tfixed (x51, x52)) (Tfixed (y51, y52)) =
    equal_nat x51 y51 andalso equal_nat x52 y52
  | equal_abi_typea (Tsint x2) (Tsint y2) = equal_nat x2 y2
  | equal_abi_typea (Tuint x1) (Tuint y1) = equal_nat x1 y1
  | equal_abi_typea Tstring Tstring = true
  | equal_abi_typea Tbytes Tbytes = true
  | equal_abi_typea Tfunction Tfunction = true
  | equal_abi_typea Tbool Tbool = true
  | equal_abi_typea Taddr Taddr = true;
val equal_abi_type = equal_abi_type ();

type 'a finite = {};

datatype 'a bit0 = Abs_bit0 of int;

fun len_of_bit0 A_ uu = times_nata (nat_of_num (Bit0 One)) (len_of A_ Type);

type 'a len = {len0_len : 'a len0};
val len0_len = #len0_len : 'a len -> 'a len0;

fun len0_bit0 A_ = {len_of = len_of_bit0 A_} : 'a bit0 len0;

fun len_bit0 A_ = {len0_len = len0_bit0 (len0_len A_)} : 'a bit0 len;

datatype 'a bit1 = Abs_bit1 of int;

fun len_of_bit1 A_ uu =
  plus_nata (times_nata (nat_of_num (Bit0 One)) (len_of A_ Type)) one_nata;

fun len0_bit1 A_ = {len_of = len_of_bit1 A_} : 'a bit1 len0;

datatype num1 = One_num1;

fun len_of_num1 uu = one_nata;

val len0_num1 = {len_of = len_of_num1} : num1 len0;

val len_num1 = {len0_len = len0_num1} : num1 len;

val one_integera : IntInf.int = (1 : IntInf.int);

val one_integer = {one = one_integera} : IntInf.int one;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

datatype token = LParen | RParen | LBrack | RBrack | Comma | Elem of char list;

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

datatype abi_value = Vuint of nat * int | Vsint of nat * int | Vaddr of int |
  Vbool of bool | Vfixed of nat * nat * rat | Vufixed of nat * nat * rat |
  Vfbytes of nat * num1 bit0 bit0 bit0 word list | Vfunction of int * int |
  Vfarray of abi_type * nat * abi_value list |
  Vtuple of abi_type list * abi_value list |
  Vbytes of num1 bit0 bit0 bit0 word list | Vstring of char list |
  Varray of abi_type * abi_value list;

datatype valueParseTree = ArrayValue of valueParseTree list |
  TupleValue of valueParseTree list | PrimaryValue of char list;

datatype typeParserState = TPS_primary of abi_type |
  TPS_array of abi_type * nat option | TPS_tuple of abi_type list;

datatype valueParserState = VPS_primary of valueParseTree |
  VPS_arrtuple of bool * valueParseTree list;

fun id x = (fn xa => xa) x;

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
  | zip xs [] = []
  | zip [] ys = [];

fun drop n [] = []
  | drop n (x :: xs) = (case n of Zero_nat => x :: xs | Suc m => drop m xs);

fun null [] = true
  | null (x :: xs) = false;

fun take n [] = []
  | take n (x :: xs) = (case n of Zero_nat => [] | Suc m => x :: take m xs);

fun minus_nat (Suc m) (Suc n) = minus_nat m n
  | minus_nat Zero_nat n = Zero_nat
  | minus_nat m Zero_nat = m;

fun bin_rest w = divide_inta w (Pos (Bit0 One));

fun bin_last w = equal_inta (modulo_inta w (Pos (Bit0 One))) one_inta;

fun bit k b = plus_inta (plus_inta (if b then one_inta else Zero_int) k) k;

fun sbintrunc Zero_nat bin =
  (if bin_last bin then uminus_int one_inta else Zero_int)
  | sbintrunc (Suc n) bin = bit (sbintrunc n (bin_rest bin)) (bin_last bin);

fun sint A_ w =
  sbintrunc (minus_nat (len_of (len0_len A_) Type) one_nata)
    (uint (len0_len A_) w);

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun those [] = SOME []
  | those (x :: xs) =
    (case x of NONE => NONE | SOME y => map_option (fn a => y :: a) (those xs));

fun funpow Zero_nat f = id
  | funpow (Suc n) f = f o funpow n f;

fun of_int a = Frct (a, one_inta);

fun word_of_int A_ k =
  Word (modulo_inta k (power power_int (Pos (Bit0 One)) (len_of A_ Type)));

fun ucast A_ B_ w = word_of_int B_ (uint A_ w);

fun fun_upd A_ f a b = (fn x => (if eq A_ x a then b else f x));

fun concat xss = foldr (fn a => fn b => a @ b) xss [];

fun bind NONE f = NONE
  | bind (SOME x) f = f x;

fun less_nat m (Suc n) = less_eq_nat m n
  | less_nat n Zero_nat = false
and less_eq_nat (Suc m) n = less_nat m n
  | less_eq_nat Zero_nat n = true;

fun divmod_nat m n =
  (if equal_nat n Zero_nat orelse less_nat m n then (Zero_nat, m)
    else let
           val a = divmod_nat (minus_nat m n) n;
           val (q, aa) = a;
         in
           (Suc q, aa)
         end);

fun decwrite1 c =
  (if equal_nat c Zero_nat
    then Chara (false, false, false, false, true, true, false, false)
    else (if equal_nat c one_nata
           then Chara (true, false, false, false, true, true, false, false)
           else (if equal_nat c (nat_of_num (Bit0 One))
                  then Chara (false, true, false, false, true, true, false,
                               false)
                  else (if equal_nat c (nat_of_num (Bit1 One))
                         then Chara (true, true, false, false, true, true,
                                      false, false)
                         else (if equal_nat c (nat_of_num (Bit0 (Bit0 One)))
                                then Chara (false, false, true, false, true,
     true, false, false)
                                else (if equal_nat c
   (nat_of_num (Bit1 (Bit0 One)))
                                       then Chara
      (true, false, true, false, true, true, false, false)
                                       else (if equal_nat c
          (nat_of_num (Bit0 (Bit1 One)))
      then Chara (false, true, true, false, true, true, false, false)
      else (if equal_nat c (nat_of_num (Bit1 (Bit1 One)))
             then Chara (true, true, true, false, true, true, false, false)
             else (if equal_nat c (nat_of_num (Bit0 (Bit0 (Bit0 One))))
                    then Chara (false, false, false, true, true, true, false,
                                 false)
                    else (if equal_nat c (nat_of_num (Bit1 (Bit0 (Bit0 One))))
                           then Chara (true, false, false, true, true, true,
false, false)
                           else (raise Fail "undefined")))))))))));

fun decwritea n =
  (if less_nat n (nat_of_num (Bit0 (Bit1 (Bit0 One)))) then [decwrite1 n]
    else let
           val (d, m) = divmod_nat n (nat_of_num (Bit0 (Bit1 (Bit0 One))));
         in
           decwrite1 m :: decwritea d
         end);

fun decwrite n = rev (decwritea n);

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun those_err [] = Inl []
  | those_err (Inl h :: t) =
    (case those_err t of Inl ta => Inl (h :: ta) | Inr a => Inr a)
  | those_err (Inr s :: uu) = Inr s;

fun shiftr1 A_ w = word_of_int A_ (bin_rest (uint A_ w));

fun numeral A_ (Bit1 n) =
  let
    val m = numeral A_ n;
  in
    plus ((plus_semigroup_add o semigroup_add_numeral) A_)
      (plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m)
      (one (one_numeral A_))
  end
  | numeral A_ (Bit0 n) =
    let
      val m = numeral A_ n;
    in
      plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m
    end
  | numeral A_ One = one (one_numeral A_);

fun digit7 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x8;

fun digit6 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x7;

fun digit5 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x6;

fun digit4 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x5;

fun digit3 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x4;

fun digit2 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x3;

fun digit1 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x2;

fun digit0 (Chara (x1, x2, x3, x4, x5, x6, x7, x8)) = x1;

fun of_char A_ c =
  foldr (fn b => fn k =>
          plus ((plus_semigroup_add o semigroup_add_numeral o
                  numeral_semiring_numeral o semiring_numeral_semiring_1 o
                  semiring_1_comm_semiring_1)
                 A_)
            (of_bool ((zero_neq_one_semiring_1 o semiring_1_comm_semiring_1) A_)
              b)
            (times
              ((times_dvd o dvd_comm_monoid_mult o
                 comm_monoid_mult_comm_semiring_1)
                A_)
              k (numeral
                  ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                     semiring_1_comm_semiring_1)
                    A_)
                  (Bit0 One))))
    [digit0 c, digit1 c, digit2 c, digit3 c, digit4 c, digit5 c, digit6 c,
      digit7 c]
    (zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
             semiring_1_comm_semiring_1)
            A_));

fun is_digit x =
  (fn c =>
    less_eq_nat
      (of_char comm_semiring_1_nat
        (Chara (false, false, false, false, true, true, false, false)))
      (of_char comm_semiring_1_nat c) andalso
      less_eq_nat (of_char comm_semiring_1_nat c)
        (of_char comm_semiring_1_nat
          (Chara (true, false, false, true, true, true, false, false))))
    x;

fun parseHexDigit x =
  (if is_digit x
    then SOME (minus_inta (of_char comm_semiring_1_int x)
                (of_char comm_semiring_1_int
                  (Chara
                    (false, false, false, false, true, true, false, false))))
    else (if less_eq_nat
               (of_char comm_semiring_1_nat
                 (Chara (true, false, false, false, false, false, true, false)))
               (of_char comm_semiring_1_nat x) andalso
               less_eq_nat (of_char comm_semiring_1_nat x)
                 (of_char comm_semiring_1_nat
                   (Chara
                     (false, true, true, false, false, false, true, false)))
           then SOME (plus_inta
                       (minus_inta (of_char comm_semiring_1_int x)
                         (of_char comm_semiring_1_int
                           (Chara
                             (true, false, false, false, false, false, true,
                               false))))
                       (Pos (Bit0 (Bit1 (Bit0 One)))))
           else (if less_eq_nat
                      (of_char comm_semiring_1_nat
                        (Chara
                          (true, false, false, false, false, true, true,
                            false)))
                      (of_char comm_semiring_1_nat x) andalso
                      less_eq_nat (of_char comm_semiring_1_nat x)
                        (of_char comm_semiring_1_nat
                          (Chara
                            (false, true, true, false, false, true, true,
                              false)))
                  then SOME (plus_inta
                              (minus_inta (of_char comm_semiring_1_int x)
                                (of_char comm_semiring_1_int
                                  (Chara
                                    (true, false, false, false, false, true,
                                      true, false))))
                              (Pos (Bit0 (Bit1 (Bit0 One)))))
                  else NONE)));

fun parseWord x =
  (fn xa => fn y =>
    (case (parseHexDigit xa, parseHexDigit y) of (NONE, _) => NONE
      | (SOME _, NONE) => NONE
      | (SOME xb, SOME ya) =>
        SOME (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
               (plus_inta (times_inta xb (Pos (Bit0 (Bit0 (Bit0 (Bit0 One))))))
                 ya))))
    x;

fun parseWords (x :: y :: z) =
  (case (parseWord x y, parseWords z) of (NONE, _) => NONE
    | (SOME _, NONE) => NONE | (SOME b, SOME bs) => SOME (b :: bs))
  | parseWords [] = SOME []
  | parseWords [x] = NONE;

fun parseWordsPrefixed x =
  (fn a =>
    (case a of [] => NONE | Chara (true, _, _, _, _, _, _, _) :: _ => NONE
      | Chara (false, true, _, _, _, _, _, _) :: _ => NONE
      | Chara (false, false, true, _, _, _, _, _) :: _ => NONE
      | Chara (false, false, false, true, _, _, _, _) :: _ => NONE
      | Chara (false, false, false, false, true, true, true, _) :: _ => NONE
      | Chara (false, false, false, false, true, true, false, true) :: _ => NONE
      | [Chara (false, false, false, false, true, true, false, false)] => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (true, _, _, _, _, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, true, _, _, _, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, true, _, _, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, true, true, true, true) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, true, true, true, false) :: tail
        => parseWords tail
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, true, true, false, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, true, false, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, false, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, false, _, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, false, _, _) :: _ => NONE
      | Chara (false, false, false, false, false, _, _, _) :: _ => NONE))
    x;

fun bit_cut_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), false)
    else let
           val (r, s) =
             IntInf.divMod (IntInf.abs k, IntInf.abs (2 : IntInf.int));
         in
           ((if IntInf.< ((0 : IntInf.int), k) then r
              else IntInf.- (IntInf.~ r, s)),
             ((s : IntInf.int) = (1 : IntInf.int)))
         end);

fun char_of_integer k = let
                          val (q0, b0) = bit_cut_integer k;
                          val (q1, b1) = bit_cut_integer q0;
                          val (q2, b2) = bit_cut_integer q1;
                          val (q3, b3) = bit_cut_integer q2;
                          val (q4, b4) = bit_cut_integer q3;
                          val (q5, b5) = bit_cut_integer q4;
                          val (q6, b6) = bit_cut_integer q5;
                          val a = bit_cut_integer q6;
                          val (_, aa) = a;
                        in
                          Chara (b0, b1, b2, b3, b4, b5, b6, aa)
                        end;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun explode s =
  map char_of_integer
    ((List.map (fn c => let val k = Char.ord c in if k < 128 then IntInf.fromInt k else raise Fail "Non-ASCII character in literal" end) 
       o String.explode)
      s);

fun bin_split Zero_nat w = (w, Zero_int)
  | bin_split (Suc n) w = let
                            val (w1, w2) = bin_split n (bin_rest w);
                          in
                            (w1, bit w2 (bin_last w))
                          end;

fun bin_rsplit_aux n m c bs =
  (if equal_nat m Zero_nat orelse equal_nat n Zero_nat then bs
    else let
           val a = bin_split n c;
           val (aa, b) = a;
         in
           bin_rsplit_aux n (minus_nat m n) aa (b :: bs)
         end);

fun bin_rsplit n w = bin_rsplit_aux n (fst w) (snd w) [];

fun word_rsplit A_ B_ w =
  map (word_of_int (len0_len B_))
    (bin_rsplit (len_of (len0_len B_) Type) (len_of A_ Type, uint A_ w));

fun dvd (A1_, A2_) a b =
  eq A1_
    (modulo ((modulo_semiring_modulo o semiring_modulo_semidom_modulo) A2_) b a)
    (zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1 o
             semiring_1_comm_semiring_1 o
             comm_semiring_1_comm_semiring_1_cancel o
             comm_semiring_1_cancel_semidom o semidom_semidom_divide o
             semidom_divide_algebraic_semidom o
             algebraic_semidom_semidom_modulo)
            A2_));

fun bita (A1_, A2_, A3_) a n =
  not (dvd (A1_, A3_)
        (numeral
          ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
             semiring_1_comm_semiring_1 o
             comm_semiring_1_comm_semiring_1_cancel o
             comm_semiring_1_cancel_semiring_modulo o
             semiring_modulo_semiring_parity o semiring_parity_semiring_bits)
            A2_)
          (Bit0 One))
        (divide
          ((divide_modulo o modulo_semiring_modulo o
             semiring_modulo_semiring_parity o semiring_parity_semiring_bits)
            A2_)
          a (power
              ((power_monoid_mult o monoid_mult_semiring_numeral o
                 semiring_numeral_semiring_1 o semiring_1_comm_semiring_1 o
                 comm_semiring_1_comm_semiring_1_cancel o
                 comm_semiring_1_cancel_semiring_modulo o
                 semiring_modulo_semiring_parity o
                 semiring_parity_semiring_bits)
                A2_)
              (numeral
                ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                   semiring_1_comm_semiring_1 o
                   comm_semiring_1_comm_semiring_1_cancel o
                   comm_semiring_1_cancel_semiring_modulo o
                   semiring_modulo_semiring_parity o
                   semiring_parity_semiring_bits)
                  A2_)
                (Bit0 One))
              n)));

fun char_of (A1_, A2_) n =
  Chara (not (dvd (A1_, (semidom_modulo_euclidean_semiring o
                          euclidean_semiring_euclidean_semiring_cancel o
                          euclidean_semiring_cancel_unique_euclidean_semiring o
                          unique_euclidean_semiring_unique_euclidean_semiring_with_nat o
                          unique_euclidean_semiring_with_nat_unique_euclidean_semiring_with_bit_shifts)
                          A2_)
               (numeral
                 ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                    semiring_1_semiring_char_0 o
                    semiring_char_0_unique_euclidean_semiring_with_nat o
                    unique_euclidean_semiring_with_nat_unique_euclidean_semiring_with_bit_shifts)
                   A2_)
                 (Bit0 One))
               n),
          bita (A1_, (semiring_bits_semiring_bit_shifts o
                       semiring_bit_shifts_unique_euclidean_semiring_with_bit_shifts)
                       A2_,
                 (semidom_modulo_euclidean_semiring o
                   euclidean_semiring_euclidean_semiring_cancel o
                   euclidean_semiring_cancel_unique_euclidean_semiring o
                   unique_euclidean_semiring_unique_euclidean_semiring_with_nat o
                   unique_euclidean_semiring_with_nat_unique_euclidean_semiring_with_bit_shifts)
                   A2_)
            n one_nata,
          bita (A1_, (semiring_bits_semiring_bit_shifts o
                       semiring_bit_shifts_unique_euclidean_semiring_with_bit_shifts)
                       A2_,
                 (semidom_modulo_euclidean_semiring o
                   euclidean_semiring_euclidean_semiring_cancel o
                   euclidean_semiring_cancel_unique_euclidean_semiring o
                   unique_euclidean_semiring_unique_euclidean_semiring_with_nat o
                   unique_euclidean_semiring_with_nat_unique_euclidean_semiring_with_bit_shifts)
                   A2_)
            n (nat_of_num (Bit0 One)),
          bita (A1_, (semiring_bits_semiring_bit_shifts o
                       semiring_bit_shifts_unique_euclidean_semiring_with_bit_shifts)
                       A2_,
                 (semidom_modulo_euclidean_semiring o
                   euclidean_semiring_euclidean_semiring_cancel o
                   euclidean_semiring_cancel_unique_euclidean_semiring o
                   unique_euclidean_semiring_unique_euclidean_semiring_with_nat o
                   unique_euclidean_semiring_with_nat_unique_euclidean_semiring_with_bit_shifts)
                   A2_)
            n (nat_of_num (Bit1 One)),
          bita (A1_, (semiring_bits_semiring_bit_shifts o
                       semiring_bit_shifts_unique_euclidean_semiring_with_bit_shifts)
                       A2_,
                 (semidom_modulo_euclidean_semiring o
                   euclidean_semiring_euclidean_semiring_cancel o
                   euclidean_semiring_cancel_unique_euclidean_semiring o
                   unique_euclidean_semiring_unique_euclidean_semiring_with_nat o
                   unique_euclidean_semiring_with_nat_unique_euclidean_semiring_with_bit_shifts)
                   A2_)
            n (nat_of_num (Bit0 (Bit0 One))),
          bita (A1_, (semiring_bits_semiring_bit_shifts o
                       semiring_bit_shifts_unique_euclidean_semiring_with_bit_shifts)
                       A2_,
                 (semidom_modulo_euclidean_semiring o
                   euclidean_semiring_euclidean_semiring_cancel o
                   euclidean_semiring_cancel_unique_euclidean_semiring o
                   unique_euclidean_semiring_unique_euclidean_semiring_with_nat o
                   unique_euclidean_semiring_with_nat_unique_euclidean_semiring_with_bit_shifts)
                   A2_)
            n (nat_of_num (Bit1 (Bit0 One))),
          bita (A1_, (semiring_bits_semiring_bit_shifts o
                       semiring_bit_shifts_unique_euclidean_semiring_with_bit_shifts)
                       A2_,
                 (semidom_modulo_euclidean_semiring o
                   euclidean_semiring_euclidean_semiring_cancel o
                   euclidean_semiring_cancel_unique_euclidean_semiring o
                   unique_euclidean_semiring_unique_euclidean_semiring_with_nat o
                   unique_euclidean_semiring_with_nat_unique_euclidean_semiring_with_bit_shifts)
                   A2_)
            n (nat_of_num (Bit0 (Bit1 One))),
          bita (A1_, (semiring_bits_semiring_bit_shifts o
                       semiring_bit_shifts_unique_euclidean_semiring_with_bit_shifts)
                       A2_,
                 (semidom_modulo_euclidean_semiring o
                   euclidean_semiring_euclidean_semiring_cancel o
                   euclidean_semiring_cancel_unique_euclidean_semiring o
                   unique_euclidean_semiring_unique_euclidean_semiring_with_nat o
                   unique_euclidean_semiring_with_nat_unique_euclidean_semiring_with_bit_shifts)
                   A2_)
            n (nat_of_num (Bit1 (Bit1 One))));

fun writeInt n =
  (if less_int n Zero_int
    then Chara (true, false, true, true, false, true, false, false) ::
           writeInt (uminus_int n)
    else (if less_int n (Pos (Bit0 (Bit1 (Bit0 One))))
           then [char_of
                   (equal_int, unique_euclidean_semiring_with_bit_shifts_int)
                   (plus_inta
                     (of_char comm_semiring_1_int
                       (Chara
                         (false, false, false, false, true, true, false,
                           false)))
                     n)]
           else writeInt (divide_inta n (Pos (Bit0 (Bit1 (Bit0 One))))) @
                  writeInt (modulo_inta n (Pos (Bit0 (Bit1 (Bit0 One)))))));

fun shiftr_word A_ w n = funpow n (shiftr1 A_) w;

fun bitAND_int x y =
  (if equal_inta x Zero_int then Zero_int
    else (if equal_inta x (uminus_int one_inta) then y
           else bit (bitAND_int (bin_rest x) (bin_rest y))
                  (bin_last x andalso bin_last y)));

fun bitAND_word A_ a b = word_of_int A_ (bitAND_int (uint A_ a) (uint A_ b));

fun less_word A_ a b = less_int (uint A_ a) (uint A_ b);

fun writeHexNibble x =
  (if less_word (len0_bit0 (len0_bit0 len0_num1)) x
        (word_of_int (len0_bit0 (len0_bit0 len0_num1))
          (Pos (Bit0 (Bit1 (Bit0 One)))))
    then char_of (equal_int, unique_euclidean_semiring_with_bit_shifts_int)
           (plus_inta
             (of_char comm_semiring_1_int
               (Chara (false, false, false, false, true, true, false, false)))
             (uint (len0_bit0 (len0_bit0 len0_num1)) x))
    else char_of (equal_int, unique_euclidean_semiring_with_bit_shifts_int)
           (minus_inta
             (plus_inta
               (of_char comm_semiring_1_int
                 (Chara (true, false, false, false, false, false, true, false)))
               (uint (len0_bit0 (len0_bit0 len0_num1)) x))
             (Pos (Bit0 (Bit1 (Bit0 One))))));

fun writeHexDigit x =
  [writeHexNibble
     (ucast (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
       (len0_bit0 (len0_bit0 len0_num1))
       (shiftr_word (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) x
         (nat_of_num (Bit0 (Bit0 One))))),
    writeHexNibble
      (ucast (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (len0_bit0 (len0_bit0 len0_num1))
        (bitAND_word (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) x
          (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
            (Pos (Bit1 (Bit1 (Bit1 One)))))))];

fun writeHex (x :: tail) = writeHexDigit x @ writeHex tail
  | writeHex [] = [];

fun writeValue (Vuint (s, value)) = writeInt value
  | writeValue (Vsint (s, value)) = writeInt value
  | writeValue (Vaddr value) =
    [Chara (false, false, false, false, true, true, false, false),
      Chara (false, false, false, true, true, true, true, false)] @
      writeHex
        (word_rsplit
          (len0_bit0
            (len0_bit0
              (len0_bit0
                (len0_bit0 (len0_bit0 (len0_bit1 (len0_bit0 len0_num1)))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (word_of_int
            (len0_bit0
              (len0_bit0
                (len0_bit0
                  (len0_bit0 (len0_bit0 (len0_bit1 (len0_bit0 len0_num1)))))))
            value))
  | writeValue (Vbool value) =
    (if value
      then [Chara (false, false, true, false, true, true, true, false),
             Chara (false, true, false, false, true, true, true, false),
             Chara (true, false, true, false, true, true, true, false),
             Chara (true, false, true, false, false, true, true, false)]
      else [Chara (false, true, true, false, false, true, true, false),
             Chara (true, false, false, false, false, true, true, false),
             Chara (false, false, true, true, false, true, true, false),
             Chara (true, true, false, false, true, true, true, false),
             Chara (true, false, true, false, false, true, true, false)])
  | writeValue (Vfixed (a, b, x)) =
    [Chara (true, false, true, false, true, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (true, false, true, false, true, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (true, true, true, true, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, true, false, false, true, true, false)]
  | writeValue (Vufixed (a, b, x)) =
    [Chara (true, false, true, false, true, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (true, false, true, false, true, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (true, true, true, true, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, true, false, false, true, true, false)]
  | writeValue (Vfbytes (s, v)) =
    [Chara (false, false, false, false, true, true, false, false),
      Chara (false, false, false, true, true, true, true, false)] @
      writeHex v
  | writeValue (Vfunction (addr, sel)) =
    ([Chara (false, false, false, false, true, true, false, false),
       Chara (false, false, false, true, true, true, true, false)] @
      writeHex
        (word_rsplit
          (len0_bit0
            (len0_bit0
              (len0_bit0
                (len0_bit0 (len0_bit0 (len0_bit1 (len0_bit0 len0_num1)))))))
          (len_bit0 (len_bit0 (len_bit0 len_num1)))
          (word_of_int
            (len0_bit0
              (len0_bit0
                (len0_bit0
                  (len0_bit0 (len0_bit0 (len0_bit1 (len0_bit0 len0_num1)))))))
            addr))) @
      [Chara (false, true, false, true, true, true, false, false)] @
        [Chara (false, false, false, false, true, true, false, false),
          Chara (false, false, false, true, true, true, true, false)] @
          writeHex
            (word_rsplit
              (len0_bit0
                (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
              (len_bit0 (len_bit0 (len_bit0 len_num1)))
              (word_of_int
                (len0_bit0
                  (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
                sel))
  | writeValue (Vfarray (t, n, vs)) =
    Chara (true, true, false, true, true, false, true, false) ::
      writeValueList vs @
        [Chara (true, false, true, true, true, false, true, false)]
  | writeValue (Vtuple (ts, vs)) =
    Chara (false, false, false, true, false, true, false, false) ::
      writeValueList vs @
        [Chara (true, false, false, true, false, true, false, false)]
  | writeValue (Varray (t, vs)) =
    Chara (true, true, false, true, true, false, true, false) ::
      writeValueList vs @
        [Chara (true, false, true, true, true, false, true, false)]
  | writeValue (Vbytes v) =
    [Chara (false, false, false, false, true, true, false, false),
      Chara (false, false, false, true, true, true, true, false)] @
      writeHex v
  | writeValue (Vstring str) =
    [Chara (false, false, false, false, true, true, false, false),
      Chara (false, false, false, true, true, true, true, false)] @
      writeHex
        (map (fn x =>
               word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                 (of_char comm_semiring_1_int x))
          str)
and writeValueList (v :: vs) =
  (if null vs then writeValue v
    else writeValue v @
           [Chara (false, false, true, true, false, true, false, false)] @
             writeValueList vs)
  | writeValueList [] = [];

fun parseBaseTypePrefix x =
  fun_upd (equal_list equal_char)
    (fun_upd (equal_list equal_char)
      (fun_upd (equal_list equal_char)
        (fun_upd (equal_list equal_char)
          (fun_upd (equal_list equal_char)
            (fun_upd (equal_list equal_char)
              (fun_upd (equal_list equal_char) (fn _ => NONE)
                [Chara (true, false, true, false, true, true, true, false),
                  Chara (true, false, false, true, false, true, true, false),
                  Chara (false, true, true, true, false, true, true, false),
                  Chara (false, false, true, false, true, true, true, false)]
                (SOME (map_option Tuint)))
              [Chara (true, false, false, true, false, true, true, false),
                Chara (false, true, true, true, false, true, true, false),
                Chara (false, false, true, false, true, true, true, false)]
              (SOME (map_option Tsint)))
            [Chara (true, false, false, false, false, true, true, false),
              Chara (false, false, true, false, false, true, true, false),
              Chara (false, false, true, false, false, true, true, false),
              Chara (false, true, false, false, true, true, true, false),
              Chara (true, false, true, false, false, true, true, false),
              Chara (true, true, false, false, true, true, true, false),
              Chara (true, true, false, false, true, true, true, false)]
            (SOME (fn a => (case a of NONE => SOME Taddr | SOME _ => NONE))))
          [Chara (false, true, true, false, false, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (false, false, true, false, true, true, true, false),
            Chara (true, false, false, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, true, true, true, false, true, true, false)]
          (SOME (fn a => (case a of NONE => SOME Tfunction | SOME _ => NONE))))
        [Chara (false, true, false, false, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false)]
        (SOME (fn a => (case a of NONE => SOME Tbool | SOME _ => NONE))))
      [Chara (false, true, false, false, false, true, true, false),
        Chara (true, false, false, true, true, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false)]
      (SOME (fn a =>
              (case a of NONE => SOME Tbytes | SOME n => SOME (Tfbytes n)))))
    [Chara (true, true, false, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, true, false, false, true, true, false)]
    (SOME (fn a => (case a of NONE => SOME Tstring | SOME _ => NONE))) x;

fun parseDigit x =
  (if is_digit x
    then SOME (minus_nat (of_char comm_semiring_1_nat x)
                (of_char comm_semiring_1_nat
                  (Chara
                    (false, false, false, false, true, true, false, false))))
    else NONE);

fun parseNatRev (x :: xs) =
  (case (parseDigit x, parseNatRev xs) of (NONE, _) => NONE
    | (SOME _, NONE) => NONE
    | (SOME d, SOME y) =>
      SOME (plus_nata d (times_nata y (nat_of_num (Bit0 (Bit1 (Bit0 One)))))))
  | parseNatRev [] = SOME Zero_nat;

fun parseNat x = (fn xa => parseNatRev (rev xa)) x;

fun splitDigitSuffix (x :: tail) parsed =
  (if is_digit x
    then (case parseNat (x :: tail) of NONE => (rev parsed @ x :: tail, NONE)
           | SOME n => (rev parsed, SOME n))
    else splitDigitSuffix tail (x :: parsed))
  | splitDigitSuffix [] parsed = (rev parsed, NONE);

fun parseBaseType x =
  (fn str =>
    let
      val (prefix, nopt) = splitDigitSuffix str [];
    in
      (case parseBaseTypePrefix prefix of NONE => NONE | SOME fna => fna nopt)
    end)
    x;

fun typeParser (LParen :: tail) st = typeParser tail (TPS_tuple [] :: st)
  | typeParser (Elem x :: tail) (TPS_array (t, NONE) :: st) =
    bind (parseNat x) (fn n => typeParser tail (TPS_array (t, SOME n) :: st))
  | typeParser (Elem x :: tail) [] =
    bind (parseBaseType x) (fn typea => typeParser tail [TPS_primary typea])
  | typeParser (Elem x :: tail) (TPS_tuple t :: ts) =
    bind (parseBaseType x)
      (fn typea => typeParser tail (TPS_primary typea :: TPS_tuple t :: ts))
  | typeParser (LBrack :: tail) (TPS_primary x :: st) =
    typeParser tail (TPS_array (x, NONE) :: st)
  | typeParser (RBrack :: tail) (TPS_array (x, nopt) :: st) =
    typeParser tail
      (TPS_primary (case nopt of NONE => Tarray x | SOME a => Tfarray (x, a)) ::
        st)
  | typeParser (RParen :: tail) (TPS_primary t :: TPS_tuple ts :: st) =
    typeParser tail (TPS_primary (Ttuple (rev (t :: ts))) :: st)
  | typeParser (Comma :: tail) (TPS_primary t :: TPS_tuple ts :: st) =
    typeParser tail (TPS_tuple (t :: ts) :: st)
  | typeParser [] [TPS_primary x] = SOME x
  | typeParser [] [] = NONE
  | typeParser [] (TPS_array (vb, vc) :: va) = NONE
  | typeParser [] (TPS_tuple vb :: va) = NONE
  | typeParser [] (v :: vb :: vc) = NONE
  | typeParser (RParen :: va) [] = NONE
  | typeParser (RParen :: va) (TPS_array (vc, vd) :: vb) = NONE
  | typeParser (RParen :: va) (TPS_tuple vc :: vb) = NONE
  | typeParser (RParen :: va) [v] = NONE
  | typeParser (RParen :: va) (v :: TPS_primary ve :: vd) = NONE
  | typeParser (RParen :: va) (v :: TPS_array (ve, vf) :: vd) = NONE
  | typeParser (LBrack :: va) [] = NONE
  | typeParser (LBrack :: va) (TPS_array (vc, vd) :: vb) = NONE
  | typeParser (LBrack :: va) (TPS_tuple vc :: vb) = NONE
  | typeParser (RBrack :: va) [] = NONE
  | typeParser (RBrack :: va) (TPS_primary vc :: vb) = NONE
  | typeParser (RBrack :: va) (TPS_tuple vc :: vb) = NONE
  | typeParser (Comma :: va) [] = NONE
  | typeParser (Comma :: va) (TPS_array (vc, vd) :: vb) = NONE
  | typeParser (Comma :: va) (TPS_tuple vc :: vb) = NONE
  | typeParser (Comma :: va) [v] = NONE
  | typeParser (Comma :: va) (v :: TPS_primary ve :: vd) = NONE
  | typeParser (Comma :: va) (v :: TPS_array (ve, vf) :: vd) = NONE
  | typeParser (Elem vb :: va) (TPS_primary vd :: vc) = NONE
  | typeParser (Elem vb :: va) (TPS_array (vd, SOME vf) :: vc) = NONE;

fun tokenScanBrackets
  (Elem [Chara (true, true, false, true, true, false, true, false)] :: tail) =
  LBrack :: tokenScanBrackets tail
  | tokenScanBrackets
    (Elem [Chara (true, false, true, true, true, false, true, false)] :: tail) =
    RBrack :: tokenScanBrackets tail
  | tokenScanBrackets (LParen :: tail) = LParen :: tokenScanBrackets tail
  | tokenScanBrackets (RParen :: tail) = RParen :: tokenScanBrackets tail
  | tokenScanBrackets (LBrack :: tail) = LBrack :: tokenScanBrackets tail
  | tokenScanBrackets (RBrack :: tail) = RBrack :: tokenScanBrackets tail
  | tokenScanBrackets (Comma :: tail) = Comma :: tokenScanBrackets tail
  | tokenScanBrackets (Elem [] :: tail) = Elem [] :: tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (false, vd, ve, vf, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (false, vd, ve, vf, vg, vh, vi, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, false, false, vf, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, false, false, vf, vg, vh, vi, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, false, ve, false, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, false, ve, false, vg, vh, vi, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, false, ve, vf, false, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, false, ve, vf, false, vh, vi, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, false, ve, vf, vg, true, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, false, ve, vf, vg, true, vi, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, false, ve, vf, vg, vh, false, vj) :: vb) :: tail) =
    Elem (Chara (vc, false, ve, vf, vg, vh, false, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, false, ve, vf, vg, vh, vi, true) :: vb) :: tail) =
    Elem (Chara (vc, false, ve, vf, vg, vh, vi, true) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, false, ve, vf, vg, vh, vi, vj) :: v :: va) :: tail) =
    Elem (Chara (vc, false, ve, vf, vg, vh, vi, vj) :: v :: va) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, true, true, vf, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, true, true, vf, vg, vh, vi, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, vd, true, false, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, true, false, vg, vh, vi, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, vd, true, vf, false, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, true, vf, false, vh, vi, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, vd, true, vf, vg, true, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, true, vf, vg, true, vi, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, vd, true, vf, vg, vh, false, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, true, vf, vg, vh, false, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, vd, true, vf, vg, vh, vi, true) :: vb) :: tail) =
    Elem (Chara (vc, vd, true, vf, vg, vh, vi, true) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, vd, true, vf, vg, vh, vi, vj) :: v :: va) :: tail) =
    Elem (Chara (vc, vd, true, vf, vg, vh, vi, vj) :: v :: va) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, vd, ve, false, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, false, vg, vh, vi, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, vd, ve, vf, false, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, vf, false, vh, vi, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, vd, ve, vf, vg, true, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, vf, vg, true, vi, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, vd, ve, vf, vg, vh, false, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, vf, vg, vh, false, vj) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets
    (Elem (Chara (vc, vd, ve, vf, vg, vh, vi, true) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, vf, vg, vh, vi, true) :: vb) ::
      tokenScanBrackets tail
  | tokenScanBrackets (Elem (va :: vc :: vd) :: tail) =
    Elem (va :: vc :: vd) :: tokenScanBrackets tail
  | tokenScanBrackets [] = [];

fun tokenScanParens
  (Elem [Chara (false, false, false, true, false, true, false, false)] :: tail)
  = LParen :: tokenScanParens tail
  | tokenScanParens
    (Elem [Chara (true, false, false, true, false, true, false, false)] :: tail)
    = RParen :: tokenScanParens tail
  | tokenScanParens (LParen :: tail) = LParen :: tokenScanParens tail
  | tokenScanParens (RParen :: tail) = RParen :: tokenScanParens tail
  | tokenScanParens (LBrack :: tail) = LBrack :: tokenScanParens tail
  | tokenScanParens (RBrack :: tail) = RBrack :: tokenScanParens tail
  | tokenScanParens (Comma :: tail) = Comma :: tokenScanParens tail
  | tokenScanParens (Elem [] :: tail) = Elem [] :: tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (true, true, ve, vf, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (true, true, ve, vf, vg, vh, vi, vj) :: vb) ::
      tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (true, vd, true, vf, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (true, vd, true, vf, vg, vh, vi, vj) :: vb) ::
      tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (true, vd, ve, false, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (true, vd, ve, false, vg, vh, vi, vj) :: vb) ::
      tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (true, vd, ve, vf, true, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (true, vd, ve, vf, true, vh, vi, vj) :: vb) ::
      tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (true, vd, ve, vf, vg, false, vi, vj) :: vb) :: tail) =
    Elem (Chara (true, vd, ve, vf, vg, false, vi, vj) :: vb) ::
      tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (true, vd, ve, vf, vg, vh, true, vj) :: vb) :: tail) =
    Elem (Chara (true, vd, ve, vf, vg, vh, true, vj) :: vb) ::
      tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (true, vd, ve, vf, vg, vh, vi, true) :: vb) :: tail) =
    Elem (Chara (true, vd, ve, vf, vg, vh, vi, true) :: vb) ::
      tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (true, vd, ve, vf, vg, vh, vi, vj) :: v :: va) :: tail) =
    Elem (Chara (true, vd, ve, vf, vg, vh, vi, vj) :: v :: va) ::
      tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (vc, true, ve, vf, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, true, ve, vf, vg, vh, vi, vj) :: vb) ::
      tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (vc, vd, true, vf, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, true, vf, vg, vh, vi, vj) :: vb) ::
      tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (vc, vd, ve, false, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, false, vg, vh, vi, vj) :: vb) ::
      tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (vc, vd, ve, vf, true, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, vf, true, vh, vi, vj) :: vb) ::
      tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (vc, vd, ve, vf, vg, false, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, vf, vg, false, vi, vj) :: vb) ::
      tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (vc, vd, ve, vf, vg, vh, true, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, vf, vg, vh, true, vj) :: vb) ::
      tokenScanParens tail
  | tokenScanParens
    (Elem (Chara (vc, vd, ve, vf, vg, vh, vi, true) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, vf, vg, vh, vi, true) :: vb) ::
      tokenScanParens tail
  | tokenScanParens (Elem (va :: vc :: vd) :: tail) =
    Elem (va :: vc :: vd) :: tokenScanParens tail
  | tokenScanParens [] = [];

fun tokenScanCommas
  (Elem [Chara (false, false, true, true, false, true, false, false)] :: tail) =
  Comma :: tokenScanCommas tail
  | tokenScanCommas (LParen :: tail) = LParen :: tokenScanCommas tail
  | tokenScanCommas (RParen :: tail) = RParen :: tokenScanCommas tail
  | tokenScanCommas (LBrack :: tail) = LBrack :: tokenScanCommas tail
  | tokenScanCommas (RBrack :: tail) = RBrack :: tokenScanCommas tail
  | tokenScanCommas (Comma :: tail) = Comma :: tokenScanCommas tail
  | tokenScanCommas (Elem [] :: tail) = Elem [] :: tokenScanCommas tail
  | tokenScanCommas
    (Elem (Chara (true, vd, ve, vf, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (true, vd, ve, vf, vg, vh, vi, vj) :: vb) ::
      tokenScanCommas tail
  | tokenScanCommas
    (Elem (Chara (vc, true, ve, vf, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, true, ve, vf, vg, vh, vi, vj) :: vb) ::
      tokenScanCommas tail
  | tokenScanCommas
    (Elem (Chara (vc, vd, false, vf, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, false, vf, vg, vh, vi, vj) :: vb) ::
      tokenScanCommas tail
  | tokenScanCommas
    (Elem (Chara (vc, vd, ve, false, vg, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, false, vg, vh, vi, vj) :: vb) ::
      tokenScanCommas tail
  | tokenScanCommas
    (Elem (Chara (vc, vd, ve, vf, true, vh, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, vf, true, vh, vi, vj) :: vb) ::
      tokenScanCommas tail
  | tokenScanCommas
    (Elem (Chara (vc, vd, ve, vf, vg, false, vi, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, vf, vg, false, vi, vj) :: vb) ::
      tokenScanCommas tail
  | tokenScanCommas
    (Elem (Chara (vc, vd, ve, vf, vg, vh, true, vj) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, vf, vg, vh, true, vj) :: vb) ::
      tokenScanCommas tail
  | tokenScanCommas
    (Elem (Chara (vc, vd, ve, vf, vg, vh, vi, true) :: vb) :: tail) =
    Elem (Chara (vc, vd, ve, vf, vg, vh, vi, true) :: vb) ::
      tokenScanCommas tail
  | tokenScanCommas (Elem (va :: vc :: vd) :: tail) =
    Elem (va :: vc :: vd) :: tokenScanCommas tail
  | tokenScanCommas [] = [];

fun tokenExplode (x :: tail) = Elem [x] :: tokenExplode tail
  | tokenExplode [] = [];

fun tokenCombine (Elem a :: Elem b :: tail) =
  tokenCombine (Elem (a @ b) :: tail)
  | tokenCombine (LParen :: tail) = LParen :: tokenCombine tail
  | tokenCombine (RParen :: tail) = RParen :: tokenCombine tail
  | tokenCombine (LBrack :: tail) = LBrack :: tokenCombine tail
  | tokenCombine (RBrack :: tail) = RBrack :: tokenCombine tail
  | tokenCombine (Comma :: tail) = Comma :: tokenCombine tail
  | tokenCombine [y] = y :: tokenCombine []
  | tokenCombine (y :: LParen :: va) = y :: tokenCombine (LParen :: va)
  | tokenCombine (y :: RParen :: va) = y :: tokenCombine (RParen :: va)
  | tokenCombine (y :: LBrack :: va) = y :: tokenCombine (LBrack :: va)
  | tokenCombine (y :: RBrack :: va) = y :: tokenCombine (RBrack :: va)
  | tokenCombine (y :: Comma :: va) = y :: tokenCombine (Comma :: va)
  | tokenCombine [] = [];

fun scanTokens x =
  (tokenCombine o tokenScanCommas o tokenScanBrackets o tokenScanParens o
    tokenExplode)
    x;

fun parseType x = (fn xa => typeParser (scanTokens xa) []) x;

fun modulo_nat m n = snd (divmod_nat m n);

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun abi_type_valid (Tuint n) =
  less_nat Zero_nat n andalso
    (less_eq_nat n
       (nat_of_num
         (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))) andalso
      equal_nat (modulo_nat n (nat_of_num (Bit0 (Bit0 (Bit0 One))))) Zero_nat)
  | abi_type_valid (Tsint n) =
    less_nat Zero_nat n andalso
      (less_eq_nat n
         (nat_of_num
           (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))) andalso
        equal_nat (modulo_nat n (nat_of_num (Bit0 (Bit0 (Bit0 One))))) Zero_nat)
  | abi_type_valid (Tfixed (m, n)) =
    less_eq_nat (nat_of_num (Bit0 (Bit0 (Bit0 One)))) m andalso
      (less_eq_nat m
         (nat_of_num
           (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))) andalso
        (equal_nat (modulo_nat m (nat_of_num (Bit0 (Bit0 (Bit0 One)))))
           Zero_nat andalso
          (less_nat Zero_nat n andalso
            less_eq_nat n
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))))))))
  | abi_type_valid (Tufixed (m, n)) =
    less_eq_nat (nat_of_num (Bit0 (Bit0 (Bit0 One)))) m andalso
      (less_eq_nat m
         (nat_of_num
           (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))) andalso
        (equal_nat (modulo_nat m (nat_of_num (Bit0 (Bit0 (Bit0 One)))))
           Zero_nat andalso
          (less_nat Zero_nat n andalso
            less_eq_nat n
              (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))))))))
  | abi_type_valid (Tfbytes m) =
    less_nat Zero_nat m andalso
      less_eq_nat m (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
  | abi_type_valid (Tfarray (t, uu)) = abi_type_valid t
  | abi_type_valid (Ttuple ts) = list_all abi_type_valid ts
  | abi_type_valid (Tarray t) = abi_type_valid t
  | abi_type_valid Taddr = true
  | abi_type_valid Tbool = true
  | abi_type_valid Tfunction = true
  | abi_type_valid Tbytes = true
  | abi_type_valid Tstring = true;

fun gen_length n (x :: xs) = gen_length (Suc n) xs
  | gen_length n [] = n;

fun size_list x = gen_length Zero_nat x;

fun decode_err s (ix, l) =
  s @ [Chara (false, false, false, false, false, true, false, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, false, false, true, false, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (true, false, false, true, true, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, false, false, false, false, true, false, false)] @
        decwrite (nat ix) @
          [Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, true, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false)] @
            decwrite (size_list l) @
              [Chara (false, true, true, true, false, true, false, false)];

fun of_nat_aux A_ inc Zero_nat i = i
  | of_nat_aux A_ inc (Suc n) i = of_nat_aux A_ inc n (inc i);

fun of_nat A_ n =
  of_nat_aux A_
    (fn i =>
      plus ((plus_semigroup_add o semigroup_add_numeral o
              numeral_semiring_numeral o semiring_numeral_semiring_1)
             A_)
        i (one ((one_numeral o numeral_semiring_numeral o
                  semiring_numeral_semiring_1)
                 A_)))
    n (zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1)
              A_));

fun abi_type_isdynamic (Tfarray (t, n)) = abi_type_isdynamic t
  | abi_type_isdynamic Tbytes = true
  | abi_type_isdynamic Tstring = true
  | abi_type_isdynamic (Tarray t) = true
  | abi_type_isdynamic (Ttuple l) = list_ex abi_type_isdynamic l
  | abi_type_isdynamic (Tuint v) = false
  | abi_type_isdynamic (Tsint v) = false
  | abi_type_isdynamic Taddr = false
  | abi_type_isdynamic Tbool = false
  | abi_type_isdynamic (Tfixed (v, va)) = false
  | abi_type_isdynamic (Tufixed (v, va)) = false
  | abi_type_isdynamic (Tfbytes v) = false
  | abi_type_isdynamic Tfunction = false;

fun abi_type_isstatic t = not (abi_type_isdynamic t);

fun abi_static_size (Tuint n) = Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))
  | abi_static_size (Tsint n) = Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))
  | abi_static_size Taddr = Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))
  | abi_static_size Tbool = Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))
  | abi_static_size (Tfixed (uu, uv)) =
    Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))
  | abi_static_size (Tufixed (uw, ux)) =
    Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))
  | abi_static_size (Tfbytes uy) = Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))
  | abi_static_size Tfunction = Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))
  | abi_static_size (Tfarray (t, n)) =
    times_inta (of_nat semiring_1_int n) (abi_static_size t)
  | abi_static_size (Ttuple ts) =
    foldl (fn a => fn x => plus_inta a (abi_static_size x)) Zero_int ts
  | abi_static_size Tbytes = Zero_int
  | abi_static_size Tstring = Zero_int
  | abi_static_size (Tarray v) = Zero_int;

fun bin_cat w Zero_nat v = w
  | bin_cat w (Suc n) v = bit (bin_cat w n (bin_rest v)) (bin_last v);

fun bin_rcat n = foldl (fn u => bin_cat u n) Zero_int;

fun word_rcat A_ B_ ws =
  word_of_int B_ (bin_rcat (len_of A_ Type) (map (uint A_) ws));

fun decode_sint l =
  sint (len_bit0
         (len_bit0
           (len_bit0
             (len_bit0 (len_bit0 (len_bit0 (len_bit0 (len_bit0 len_num1))))))))
    (word_rcat (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
      (len0_bit0
        (len0_bit0
          (len0_bit0
            (len0_bit0
              (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))))))
      (take (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))) l));

fun integer_of_int k =
  (if less_int k Zero_int then IntInf.~ (integer_of_int (uminus_int k))
    else (if equal_inta k Zero_int then (0 : IntInf.int)
           else let
                  val l =
                    IntInf.* ((2 : IntInf.int), integer_of_int
          (divide_inta k (Pos (Bit0 One))));
                  val j = modulo_inta k (Pos (Bit0 One));
                in
                  (if equal_inta j Zero_int then l
                    else IntInf.+ (l, (1 : IntInf.int)))
                end));

fun bytes_to_string bs =
  map (fn b =>
        char_of_integer
          (integer_of_int
            (uint (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) b)))
    bs;

fun abi_get_type (Vuint (n, uu)) = Tuint n
  | abi_get_type (Vsint (n, uv)) = Tsint n
  | abi_get_type (Vaddr uw) = Taddr
  | abi_get_type (Vbool ux) = Tbool
  | abi_get_type (Vfixed (m, n, uy)) = Tfixed (m, n)
  | abi_get_type (Vufixed (m, n, uz)) = Tufixed (m, n)
  | abi_get_type (Vfbytes (n, va)) = Tfbytes n
  | abi_get_type (Vfunction (vb, vc)) = Tfunction
  | abi_get_type (Vfarray (t, n, vd)) = Tfarray (t, n)
  | abi_get_type (Vtuple (ts, ve)) = Ttuple ts
  | abi_get_type (Vbytes vf) = Tbytes
  | abi_get_type (Vstring vg) = Tstring
  | abi_get_type (Varray (t, vh)) = Tarray t;

fun farray_value_valid_aux t n l =
  equal_nat (size_list l) n andalso
    list_all (fn v => equal_abi_typea (abi_get_type v) t) l;

fun tuple_value_valid_aux ts vs =
  equal_lista equal_abi_type (map abi_get_type vs) ts;

fun max_uint n = minus_inta (power power_int (Pos (Bit0 One)) n) one_inta;

fun uint_value_valid n i =
  less_eq_int Zero_int i andalso less_eq_int i (max_uint n);

fun function_value_valid i1 i2 =
  uint_value_valid
    (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))) i1 andalso
    uint_value_valid (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))) i2;

fun skip_padding n =
  (case divmod_nat n (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
    of (_, Zero_nat) => n
    | (_, Suc nat) =>
      minus_nat
        (plus_nata n (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
        (Suc nat));

fun replicate Zero_nat x = []
  | replicate (Suc n) x = x :: replicate n x;

fun check_padding n l =
  let
    val p = skip_padding n;
  in
    less_eq_nat p (size_list l) andalso
      equal_lista (equal_word (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))
        (drop n (take p l))
        (replicate (minus_nat p n)
          (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) Zero_int))
  end;

fun decode_function_sel bs =
  (if check_padding (nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 One))))) bs
    then SOME (uint (len0_bit0
                      (len0_bit0
                        (len0_bit0
                          (len0_bit0
                            (len0_bit0 (len0_bit1 (len0_bit0 len0_num1)))))))
                 (word_rcat (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                   (len0_bit0
                     (len0_bit0
                       (len0_bit0
                         (len0_bit0
                           (len0_bit0 (len0_bit1 (len0_bit0 len0_num1)))))))
                   (take (nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 One))))) bs)),
                uint (len0_bit0
                       (len0_bit0
                         (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
                  (word_rcat (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                    (len0_bit0
                      (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
                    (take (nat_of_num (Bit0 (Bit0 One)))
                      (drop (nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 One))))) bs))))
    else NONE);

fun int_of_fixed n r =
  let
    val (num, den) =
      quotient_of
        (times_rata r
          (power power_rat (of_int (Pos (Bit0 (Bit1 (Bit0 One))))) n));
  in
    (if equal_inta den one_inta then SOME num else NONE)
  end;

fun ufixed_value_valid m n r =
  (case int_of_fixed n r of NONE => false
    | SOME i => less_eq_int Zero_int i andalso less_eq_int i (max_uint m));

fun fbytes_value_valid n l = equal_nat (size_list l) n;

fun min_sint n =
  times_inta (uminus_int one_inta)
    (power power_int (Pos (Bit0 One)) (minus_nat n one_nata));

fun max_sint n =
  minus_inta (power power_int (Pos (Bit0 One)) (minus_nat n one_nata)) one_inta;

fun fixed_value_valid m n r =
  (case int_of_fixed n r of NONE => false
    | SOME i => less_eq_int (min_sint m) i andalso less_eq_int i (max_sint m));

fun sint_value_valid n i =
  less_eq_int (min_sint n) i andalso less_eq_int i (max_sint n);

fun addr_value_valid i =
  uint_value_valid
    (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))) i;

fun divide_rat p q = Frct let
                            val a = quotient_of p;
                            val (aa, c) = a;
                            val b = quotient_of q;
                            val (ba, d) = b;
                          in
                            normalize (times_inta aa d, times_inta c ba)
                          end;

fun decode_uint l =
  uint (len0_bit0
         (len0_bit0
           (len0_bit0
             (len0_bit0
               (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))))))
    (word_rcat (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
      (len0_bit0
        (len0_bit0
          (len0_bit0
            (len0_bit0
              (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))))))
      (take (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))) l));

fun decode_ufixed n l =
  let
    val i = decode_uint l;
  in
    divide_rat (of_int i)
      (power power_rat (of_int (Pos (Bit0 (Bit1 (Bit0 One))))) n)
  end;

fun decode_fbytes n l = (if check_padding n l then SOME (take n l) else NONE);

fun decode_fixed n l =
  let
    val i = decode_sint l;
  in
    divide_rat (of_int i)
      (power power_rat (of_int (Pos (Bit0 (Bit1 (Bit0 One))))) n)
  end;

fun decode_bool l =
  let
    val i = decode_uint l;
  in
    (if equal_inta i Zero_int then SOME false
      else (if equal_inta i one_inta then SOME true else NONE))
  end;

fun decode_static (Tuint n) (ix, l) =
  let
    val la = drop (nat ix) l;
    val res = decode_uint la;
  in
    (if uint_value_valid n res then Inl (Vuint (n, res))
      else Inr (decode_err
                 [Chara (true, false, false, true, false, false, true, false),
                   Chara (false, true, true, true, false, true, true, false),
                   Chara (false, true, true, false, true, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (true, false, false, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (true, false, true, false, true, true, true, false),
                   Chara (true, false, false, true, false, true, true, false),
                   Chara (false, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, true, true, true, false)]
                 (ix, l)))
  end
  | decode_static (Tsint n) (ix, l) =
    let
      val la = drop (nat ix) l;
      val res = decode_sint la;
    in
      (if sint_value_valid n res then Inl (Vsint (n, res))
        else Inr (decode_err
                   [Chara (true, false, false, true, false, false, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, true, true, false, true, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, false, true, false, false, true, true,
                             false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, true, false, false, true, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, false, true, false, true, true, true, false)]
                   (ix, l)))
    end
  | decode_static Taddr (ix, l) =
    let
      val la = drop (nat ix) l;
      val res = decode_uint la;
    in
      (if addr_value_valid res then Inl (Vaddr res)
        else Inr (decode_err
                   [Chara (true, false, false, true, false, false, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, true, true, false, true, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, false, true, false, false, true, true,
                             false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, false, true, false, false, true, true,
                             false),
                     Chara (false, false, true, false, false, true, true,
                             false),
                     Chara (false, true, false, false, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (true, true, false, false, true, true, true, false),
                     Chara (true, true, false, false, true, true, true, false)]
                   (ix, l)))
    end
  | decode_static Tbool (ix, l) =
    let
      val la = drop (nat ix) l;
    in
      (case decode_bool la
        of NONE =>
          Inr (decode_err
                [Chara (true, false, false, true, false, false, true, false),
                  Chara (false, true, true, true, false, true, true, false),
                  Chara (false, true, true, false, true, true, true, false),
                  Chara (true, false, false, false, false, true, true, false),
                  Chara (false, false, true, true, false, true, true, false),
                  Chara (true, false, false, true, false, true, true, false),
                  Chara (false, false, true, false, false, true, true, false),
                  Chara (false, false, false, false, false, true, false, false),
                  Chara (false, true, false, false, false, true, true, false),
                  Chara (true, true, true, true, false, true, true, false),
                  Chara (true, true, true, true, false, true, true, false),
                  Chara (false, false, true, true, false, true, true, false)]
                (ix, l))
        | SOME b => Inl (Vbool b))
    end
  | decode_static (Tfixed (m, n)) (ix, l) =
    let
      val la = drop (nat ix) l;
      val res = decode_fixed n la;
    in
      (if fixed_value_valid m n res then Inl (Vfixed (m, n, res))
        else Inr (decode_err
                   [Chara (true, false, false, true, false, false, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, true, true, false, true, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, false, true, false, false, true, true,
                             false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, true, true, false, false, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, false, false, true, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, true, false, false, true, true,
                             false)]
                   (ix, l)))
    end
  | decode_static (Tufixed (m, n)) (ix, l) =
    let
      val la = drop (nat ix) l;
      val res = decode_ufixed n la;
    in
      (if ufixed_value_valid m n res then Inl (Vufixed (m, n, res))
        else Inr (decode_err
                   [Chara (true, false, false, true, false, false, true, false),
                     Chara (false, true, true, true, false, true, true, false),
                     Chara (false, true, true, false, true, true, true, false),
                     Chara (true, false, false, false, false, true, true,
                             false),
                     Chara (false, false, true, true, false, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, false, true, false, false, true, true,
                             false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (true, false, true, false, true, true, true, false),
                     Chara (false, true, true, false, false, true, true, false),
                     Chara (true, false, false, true, false, true, true, false),
                     Chara (false, false, false, true, true, true, true, false),
                     Chara (true, false, true, false, false, true, true, false),
                     Chara (false, false, true, false, false, true, true,
                             false)]
                   (ix, l)))
    end
  | decode_static (Tfbytes n) (ix, l) =
    let
      val la = drop (nat ix) l;
    in
      (case decode_fbytes n la
        of NONE =>
          Inr (decode_err
                [Chara (true, false, false, true, false, true, true, false),
                  Chara (false, true, true, true, false, true, true, false),
                  Chara (false, true, true, false, true, true, true, false),
                  Chara (true, false, false, false, false, true, true, false),
                  Chara (false, false, true, true, false, true, true, false),
                  Chara (true, false, false, true, false, true, true, false),
                  Chara (false, false, true, false, false, true, true, false),
                  Chara (false, false, false, false, false, true, false, false),
                  Chara (false, true, true, false, false, true, true, false),
                  Chara (false, true, false, false, false, true, true, false),
                  Chara (true, false, false, true, true, true, true, false),
                  Chara (false, false, true, false, true, true, true, false),
                  Chara (true, false, true, false, false, true, true, false),
                  Chara (true, true, false, false, true, true, true, false),
                  Chara (false, false, false, false, false, true, false, false),
                  Chara (false, false, false, false, true, true, true, false),
                  Chara (true, false, false, false, false, true, true, false),
                  Chara (false, false, true, false, false, true, true, false),
                  Chara (false, false, true, false, false, true, true, false),
                  Chara (true, false, false, true, false, true, true, false),
                  Chara (false, true, true, true, false, true, true, false),
                  Chara (true, true, true, false, false, true, true, false)]
                (ix, l))
        | SOME res =>
          (if fbytes_value_valid n res then Inl (Vfbytes (n, res))
            else Inr (decode_err
                       [Chara (true, false, false, true, false, false, true,
                                false),
                         Chara (false, true, true, true, false, true, true,
                                 false),
                         Chara (false, true, true, false, true, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (false, false, true, true, false, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (false, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, true, true, false, false, true, true,
                                 false),
                         Chara (false, true, false, false, false, true, true,
                                 false),
                         Chara (true, false, false, true, true, true, true,
                                 false),
                         Chara (false, false, true, false, true, true, true,
                                 false),
                         Chara (true, false, true, false, false, true, true,
                                 false),
                         Chara (true, true, false, false, true, true, true,
                                 false)]
                       (ix, l))))
    end
  | decode_static Tfunction (ix, l) =
    let
      val la = drop (nat ix) l;
    in
      (case decode_function_sel la
        of NONE =>
          Inr (decode_err
                [Chara (true, false, false, true, false, true, true, false),
                  Chara (false, true, true, true, false, true, true, false),
                  Chara (false, true, true, false, true, true, true, false),
                  Chara (true, false, false, false, false, true, true, false),
                  Chara (false, false, true, true, false, true, true, false),
                  Chara (true, false, false, true, false, true, true, false),
                  Chara (false, false, true, false, false, true, true, false),
                  Chara (false, false, false, false, false, true, false, false),
                  Chara (false, true, true, false, false, true, true, false),
                  Chara (true, false, true, false, true, true, true, false),
                  Chara (false, true, true, true, false, true, true, false),
                  Chara (true, true, false, false, false, true, true, false),
                  Chara (false, false, true, false, true, true, true, false),
                  Chara (true, false, false, true, false, true, true, false),
                  Chara (true, true, true, true, false, true, true, false),
                  Chara (false, true, true, true, false, true, true, false),
                  Chara (false, false, false, false, false, true, false, false),
                  Chara (false, false, false, false, true, true, true, false),
                  Chara (true, false, false, false, false, true, true, false),
                  Chara (false, false, true, false, false, true, true, false),
                  Chara (false, false, true, false, false, true, true, false),
                  Chara (true, false, false, true, false, true, true, false),
                  Chara (false, true, true, true, false, true, true, false),
                  Chara (true, true, true, false, false, true, true, false)]
                (ix, l))
        | SOME (i, j) =>
          (if function_value_valid i j then Inl (Vfunction (i, j))
            else Inr (decode_err
                       [Chara (true, false, false, true, false, false, true,
                                false),
                         Chara (false, true, true, true, false, true, true,
                                 false),
                         Chara (false, true, true, false, true, true, true,
                                 false),
                         Chara (true, false, false, false, false, true, true,
                                 false),
                         Chara (false, false, true, true, false, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (false, false, true, false, false, true, true,
                                 false),
                         Chara (false, false, false, false, false, true, false,
                                 false),
                         Chara (false, true, true, false, false, true, true,
                                 false),
                         Chara (true, false, true, false, true, true, true,
                                 false),
                         Chara (false, true, true, true, false, true, true,
                                 false),
                         Chara (true, true, false, false, false, true, true,
                                 false),
                         Chara (false, false, true, false, true, true, true,
                                 false),
                         Chara (true, false, false, true, false, true, true,
                                 false),
                         Chara (true, true, true, true, false, true, true,
                                 false),
                         Chara (false, true, true, true, false, true, true,
                                 false)]
                       (ix, l))))
    end
  | decode_static (Tfarray (t, n)) (ix, l) =
    (case decode_static_tup (replicate n t) (ix, l)
      of Inl vs =>
        (if farray_value_valid_aux t n vs then Inl (Vfarray (t, n, vs))
          else Inr (decode_err
                     [Chara (true, false, false, true, false, false, true,
                              false),
                       Chara (false, true, true, true, false, true, true,
                               false),
                       Chara (false, true, true, false, true, true, true,
                               false),
                       Chara (true, false, false, false, false, true, true,
                               false),
                       Chara (false, false, true, true, false, true, true,
                               false),
                       Chara (true, false, false, true, false, true, true,
                               false),
                       Chara (false, false, true, false, false, true, true,
                               false),
                       Chara (false, false, false, false, false, true, false,
                               false),
                       Chara (false, true, true, false, false, true, true,
                               false),
                       Chara (true, false, false, false, false, true, true,
                               false),
                       Chara (false, true, false, false, true, true, true,
                               false),
                       Chara (false, true, false, false, true, true, true,
                               false),
                       Chara (true, false, false, false, false, true, true,
                               false),
                       Chara (true, false, false, true, true, true, true,
                               false)]
                     (ix, l)))
      | Inr a => Inr a)
  | decode_static (Ttuple ts) (ix, l) =
    (case decode_static_tup ts (ix, l)
      of Inl vs =>
        (if tuple_value_valid_aux ts vs then Inl (Vtuple (ts, vs))
          else Inr (decode_err
                     [Chara (true, false, false, true, false, false, true,
                              false),
                       Chara (false, true, true, true, false, true, true,
                               false),
                       Chara (false, true, true, false, true, true, true,
                               false),
                       Chara (true, false, false, false, false, true, true,
                               false),
                       Chara (false, false, true, true, false, true, true,
                               false),
                       Chara (true, false, false, true, false, true, true,
                               false),
                       Chara (false, false, true, false, false, true, true,
                               false),
                       Chara (false, false, false, false, false, true, false,
                               false),
                       Chara (false, false, true, false, true, true, true,
                               false),
                       Chara (true, false, true, false, true, true, true,
                               false),
                       Chara (false, false, false, false, true, true, true,
                               false),
                       Chara (false, false, true, true, false, true, true,
                               false),
                       Chara (true, false, true, false, false, true, true,
                               false)]
                     (ix, l)))
      | Inr a => Inr a)
  | decode_static Tbytes (ix, l) =
    Inr (decode_err
          [Chara (false, true, false, false, true, false, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, true, true, true, false),
            Chara (false, false, true, false, true, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, false, true, false, true, true, true, false),
            Chara (true, false, false, true, false, true, true, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, false, false, true, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (true, true, false, false, true, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, false, true, true, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (true, false, true, true, false, true, true, false),
            Chara (true, false, false, true, false, true, true, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (true, false, false, true, true, true, true, false)]
          (ix, l))
  | decode_static Tstring (ix, l) =
    Inr (decode_err
          [Chara (false, true, false, false, true, false, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, true, true, true, false),
            Chara (false, false, true, false, true, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, false, true, false, true, true, true, false),
            Chara (true, false, false, true, false, true, true, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, false, false, true, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (true, true, false, false, true, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, false, true, true, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (true, false, true, true, false, true, true, false),
            Chara (true, false, false, true, false, true, true, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (true, false, false, true, true, true, true, false)]
          (ix, l))
  | decode_static (Tarray v) (ix, l) =
    Inr (decode_err
          [Chara (false, true, false, false, true, false, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, true, true, true, false),
            Chara (false, false, true, false, true, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, false, true, false, true, true, true, false),
            Chara (true, false, false, true, false, true, true, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, false, false, true, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (true, true, false, false, true, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, false, true, true, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (true, false, true, true, false, true, true, false),
            Chara (true, false, false, true, false, true, true, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (true, false, false, true, true, true, true, false)]
          (ix, l))
and decode_static_tup [] (ix, l) = Inl []
  | decode_static_tup (t :: ts) (ix, l) =
    (case decode_static t (ix, l)
      of Inl v =>
        (case decode_static_tup ts (plus_inta ix (abi_static_size t), l)
          of Inl vs => Inl (v :: vs) | Inr a => Inr a)
      | Inr a => Inr a);

fun decodeb t (ix, l) =
  (if less_int ix Zero_int
    then Inr (decode_err
               [Chara (false, false, true, false, true, false, true, false),
                 Chara (false, true, false, false, true, true, true, false),
                 Chara (true, false, false, true, false, true, true, false),
                 Chara (true, false, true, false, false, true, true, false),
                 Chara (false, false, true, false, false, true, true, false),
                 Chara (false, false, false, false, false, true, false, false),
                 Chara (false, false, true, false, true, true, true, false),
                 Chara (true, true, true, true, false, true, true, false),
                 Chara (false, false, false, false, false, true, false, false),
                 Chara (false, false, true, false, false, true, true, false),
                 Chara (true, false, true, false, false, true, true, false),
                 Chara (true, true, false, false, false, true, true, false),
                 Chara (true, true, true, true, false, true, true, false),
                 Chara (false, false, true, false, false, true, true, false),
                 Chara (true, false, true, false, false, true, true, false),
                 Chara (false, false, false, false, false, true, false, false),
                 Chara (true, false, false, false, false, true, true, false),
                 Chara (false, false, true, false, true, true, true, false),
                 Chara (false, false, false, false, false, true, false, false),
                 Chara (true, false, false, false, false, true, true, false),
                 Chara (false, false, false, false, false, true, false, false),
                 Chara (false, true, true, true, false, true, true, false),
                 Chara (true, false, true, false, false, true, true, false),
                 Chara (true, true, true, false, false, true, true, false),
                 Chara (true, false, false, false, false, true, true, false),
                 Chara (false, false, true, false, true, true, true, false),
                 Chara (true, false, false, true, false, true, true, false),
                 Chara (false, true, true, false, true, true, true, false),
                 Chara (true, false, true, false, false, true, true, false),
                 Chara (false, false, false, false, false, true, false, false),
                 Chara (true, false, false, true, false, true, true, false),
                 Chara (false, true, true, true, false, true, true, false),
                 Chara (false, false, true, false, false, true, true, false),
                 Chara (true, false, true, false, false, true, true, false),
                 Chara (false, false, false, true, true, true, true, false)]
               (ix, l))
    else (if less_int (of_nat semiring_1_int (size_list l)) ix
           then Inr (decode_err
                      [Chara (false, false, true, false, true, false, true,
                               false),
                        Chara (false, true, false, false, true, true, true,
                                false),
                        Chara (true, false, false, true, false, true, true,
                                false),
                        Chara (true, false, true, false, false, true, true,
                                false),
                        Chara (false, false, true, false, false, true, true,
                                false),
                        Chara (false, false, false, false, false, true, false,
                                false),
                        Chara (false, false, true, false, true, true, true,
                                false),
                        Chara (true, true, true, true, false, true, true,
                                false),
                        Chara (false, false, false, false, false, true, false,
                                false),
                        Chara (false, false, true, false, false, true, true,
                                false),
                        Chara (true, false, true, false, false, true, true,
                                false),
                        Chara (true, true, false, false, false, true, true,
                                false),
                        Chara (true, true, true, true, false, true, true,
                                false),
                        Chara (false, false, true, false, false, true, true,
                                false),
                        Chara (true, false, true, false, false, true, true,
                                false),
                        Chara (false, false, false, false, false, true, false,
                                false),
                        Chara (true, false, false, false, false, true, true,
                                false),
                        Chara (false, false, true, false, true, true, true,
                                false),
                        Chara (false, false, false, false, false, true, false,
                                false),
                        Chara (true, false, false, false, false, true, true,
                                false),
                        Chara (false, true, true, true, false, true, true,
                                false),
                        Chara (false, false, false, false, false, true, false,
                                false),
                        Chara (true, false, false, true, false, true, true,
                                false),
                        Chara (false, true, true, true, false, true, true,
                                false),
                        Chara (false, false, true, false, false, true, true,
                                false),
                        Chara (true, false, true, false, false, true, true,
                                false),
                        Chara (false, false, false, true, true, true, true,
                                false),
                        Chara (false, false, false, false, false, true, false,
                                false),
                        Chara (true, true, true, true, false, true, true,
                                false),
                        Chara (true, false, true, false, true, true, true,
                                false),
                        Chara (false, false, true, false, true, true, true,
                                false),
                        Chara (false, false, false, false, false, true, false,
                                false),
                        Chara (true, true, true, true, false, true, true,
                                false),
                        Chara (false, true, true, false, false, true, true,
                                false),
                        Chara (false, false, false, false, false, true, false,
                                false),
                        Chara (false, true, false, false, true, true, true,
                                false),
                        Chara (true, false, false, false, false, true, true,
                                false),
                        Chara (false, true, true, true, false, true, true,
                                false),
                        Chara (true, true, true, false, false, true, true,
                                false),
                        Chara (true, false, true, false, false, true, true,
                                false)]
                      (ix, l))
           else let
                  val la = drop (nat ix) l;
                in
                  (if abi_type_isstatic t
                    then (if less_int (of_nat semiring_1_int (size_list l))
                               (plus_inta (abi_static_size t) ix)
                           then Inr (decode_err
                                      [Chara
 (false, false, true, false, true, false, true, false),
Chara (true, true, true, true, false, true, true, false),
Chara (true, true, true, true, false, true, true, false),
Chara (false, false, false, false, false, true, false, false),
Chara (false, true, true, false, false, true, true, false),
Chara (true, false, true, false, false, true, true, false),
Chara (true, true, true, false, true, true, true, false),
Chara (false, false, false, false, false, true, false, false),
Chara (false, true, false, false, false, true, true, false),
Chara (true, false, false, true, true, true, true, false),
Chara (false, false, true, false, true, true, true, false),
Chara (true, false, true, false, false, true, true, false),
Chara (true, true, false, false, true, true, true, false),
Chara (false, false, false, false, false, true, false, false),
Chara (false, true, true, false, false, true, true, false),
Chara (true, true, true, true, false, true, true, false),
Chara (false, true, false, false, true, true, true, false),
Chara (false, false, false, false, false, true, false, false),
Chara (true, true, true, false, false, true, true, false),
Chara (true, false, false, true, false, true, true, false),
Chara (false, true, true, false, true, true, true, false),
Chara (true, false, true, false, false, true, true, false),
Chara (false, true, true, true, false, true, true, false),
Chara (false, false, false, false, false, true, false, false),
Chara (true, true, false, false, true, true, true, false),
Chara (false, false, true, false, true, true, true, false),
Chara (true, false, false, false, false, true, true, false),
Chara (false, false, true, false, true, true, true, false),
Chara (true, false, false, true, false, true, true, false),
Chara (true, true, false, false, false, true, true, false),
Chara (false, false, false, false, false, true, false, false),
Chara (false, false, true, false, true, true, true, false),
Chara (true, false, false, true, true, true, true, false),
Chara (false, false, false, false, true, true, true, false),
Chara (true, false, true, false, false, true, true, false)]
                                      (ix, l))
                           else (case decode_static t (ix, l)
                                  of Inl v => Inl (v, abi_static_size t)
                                  | Inr a => Inr a))
                    else (case t
                           of Tuint _ =>
                             Inr (decode_err
                                   [Chara (false, false, true, false, true,
    false, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (true, false, true, false, true,
     true, true, false),
                                     Chara (false, false, true, true, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, true, false, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (true, false, false, false, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false)]
                                   (ix, l))
                           | Tsint _ =>
                             Inr (decode_err
                                   [Chara (false, false, true, false, true,
    false, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (true, false, true, false, true,
     true, true, false),
                                     Chara (false, false, true, true, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, true, false, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (true, false, false, false, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false)]
                                   (ix, l))
                           | Taddr =>
                             Inr (decode_err
                                   [Chara (false, false, true, false, true,
    false, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (true, false, true, false, true,
     true, true, false),
                                     Chara (false, false, true, true, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, true, false, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (true, false, false, false, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false)]
                                   (ix, l))
                           | Tbool =>
                             Inr (decode_err
                                   [Chara (false, false, true, false, true,
    false, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (true, false, true, false, true,
     true, true, false),
                                     Chara (false, false, true, true, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, true, false, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (true, false, false, false, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false)]
                                   (ix, l))
                           | Tfixed (_, _) =>
                             Inr (decode_err
                                   [Chara (false, false, true, false, true,
    false, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (true, false, true, false, true,
     true, true, false),
                                     Chara (false, false, true, true, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, true, false, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (true, false, false, false, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false)]
                                   (ix, l))
                           | Tufixed (_, _) =>
                             Inr (decode_err
                                   [Chara (false, false, true, false, true,
    false, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (true, false, true, false, true,
     true, true, false),
                                     Chara (false, false, true, true, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, true, false, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (true, false, false, false, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false)]
                                   (ix, l))
                           | Tfbytes _ =>
                             Inr (decode_err
                                   [Chara (false, false, true, false, true,
    false, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (true, false, true, false, true,
     true, true, false),
                                     Chara (false, false, true, true, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, true, false, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (true, false, false, false, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false)]
                                   (ix, l))
                           | Tfunction =>
                             Inr (decode_err
                                   [Chara (false, false, true, false, true,
    false, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, false, false, true, false,
     true, true, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, true,
     true, true, false),
                                     Chara (false, false, false, true, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (true, false, true, false, true,
     true, true, false),
                                     Chara (false, false, true, true, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, true, false, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false),
                                     Chara (true, false, false, false, false,
     true, true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (false, false, false, false, false,
     true, false, false),
                                     Chara (true, true, false, false, false,
     true, true, false),
                                     Chara (true, true, true, true, false, true,
     true, false),
                                     Chara (false, false, true, false, false,
     true, true, false),
                                     Chara (true, false, true, false, false,
     true, true, false)]
                                   (ix, l))
                           | Tfarray (ta, n) =>
                             let
                               val ts =
                                 replicate (nat (of_nat semiring_1_int n)) ta;
                             in
                               (case decode_dyn_tuple_heads ts Zero_int (ix, l)
                                 of Inl (vos,
  (idxs, (byteoffset, bytes_parsed)))
                                   => (case
decode_dyn_tuple_tails idxs ts vos byteoffset (ix, l)
of Inl (vs, bytes_parseda) =>
  Inl (Vfarray (ta, n, vs), plus_inta bytes_parsed bytes_parseda)
| Inr a => Inr a)
                                 | Inr a => Inr a)
                             end
                           | Ttuple ts =>
                             (case decode_dyn_tuple_heads ts Zero_int (ix, l)
                               of Inl (vos, (idxs, (byteoffset, bytes_parsed)))
                                 => (case decode_dyn_tuple_tails idxs ts vos
    byteoffset (ix, l)
                                      of Inl (vs, bytes_parseda) =>
Inl (Vtuple (ts, vs), plus_inta bytes_parsed bytes_parseda)
                                      | Inr a => Inr a)
                               | Inr a => Inr a)
                           | Tbytes =>
                             (if less_int (of_nat semiring_1_int (size_list l))
                                   (plus_inta
                                     (Pos (Bit0
    (Bit0 (Bit0 (Bit0 (Bit0 One))))))
                                     ix)
                               then Inr (decode_err
  [Chara (false, false, true, false, true, false, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, false, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, true, true, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, false, false, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, true, false, true, true, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, false, false, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (true, false, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, false, true, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false)]
  (ix, l))
                               else let
                                      val sz =
decode_uint (take (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))) la);
                                    in
                                      (if less_int
    (of_nat semiring_1_int (size_list l))
    (plus_inta (plus_inta sz (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))) ix)
then Inr (decode_err
           [Chara (false, true, true, false, false, false, true, false),
             Chara (true, false, true, false, false, true, true, false),
             Chara (true, true, true, false, true, true, true, false),
             Chara (true, false, true, false, false, true, true, false),
             Chara (false, true, false, false, true, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (false, true, false, false, false, true, true, false),
             Chara (true, false, false, true, true, true, true, false),
             Chara (false, false, true, false, true, true, true, false),
             Chara (true, false, true, false, false, true, true, false),
             Chara (true, true, false, false, true, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (false, true, false, false, true, true, true, false),
             Chara (true, false, true, false, false, true, true, false),
             Chara (true, false, true, true, false, true, true, false),
             Chara (true, false, false, false, false, true, true, false),
             Chara (true, false, false, true, false, true, true, false),
             Chara (false, true, true, true, false, true, true, false),
             Chara (true, false, false, true, false, true, true, false),
             Chara (false, true, true, true, false, true, true, false),
             Chara (true, true, true, false, false, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (false, false, true, false, true, true, true, false),
             Chara (false, false, false, true, false, true, true, false),
             Chara (true, false, false, false, false, true, true, false),
             Chara (false, true, true, true, false, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (false, true, false, false, false, true, true, false),
             Chara (true, false, false, true, true, true, true, false),
             Chara (false, false, true, false, true, true, true, false),
             Chara (true, false, true, false, false, true, true, false),
             Chara (true, true, false, false, true, true, true, false),
             Chara (false, false, true, false, true, true, true, false),
             Chara (false, true, false, false, true, true, true, false),
             Chara (true, false, true, false, false, true, true, false),
             Chara (true, false, false, false, false, true, true, false),
             Chara (true, false, true, true, false, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (true, true, false, false, true, true, true, false),
             Chara (true, false, false, true, false, true, true, false),
             Chara (false, true, false, true, true, true, true, false),
             Chara (true, false, true, false, false, true, true, false)]
           (ix, l))
else (if check_padding (nat sz)
           (drop (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))) la)
       then Inl (Vbytes
                   (take (nat sz)
                     (drop (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
                       la)),
                  plus_inta (of_nat semiring_1_int (skip_padding (nat sz)))
                    (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
       else Inr (decode_err
                  [Chara (true, false, false, true, false, false, true, false),
                    Chara (false, true, true, true, false, true, true, false),
                    Chara (false, true, true, false, true, true, true, false),
                    Chara (true, false, false, false, false, true, true, false),
                    Chara (false, false, true, true, false, true, true, false),
                    Chara (true, false, false, true, false, true, true, false),
                    Chara (false, false, true, false, false, true, true, false),
                    Chara (false, false, false, false, false, true, false,
                            false),
                    Chara (false, true, false, false, false, true, true, false),
                    Chara (true, false, false, true, true, true, true, false),
                    Chara (false, false, true, false, true, true, true, false),
                    Chara (true, false, true, false, false, true, true, false),
                    Chara (true, true, false, false, true, true, true, false),
                    Chara (false, false, false, false, false, true, false,
                            false),
                    Chara (false, false, false, false, true, true, true, false),
                    Chara (true, false, false, false, false, true, true, false),
                    Chara (false, false, true, false, false, true, true, false),
                    Chara (false, false, true, false, false, true, true, false),
                    Chara (true, false, false, true, false, true, true, false),
                    Chara (false, true, true, true, false, true, true, false),
                    Chara (true, true, true, false, false, true, true, false)]
                  (ix, l))))
                                    end)
                           | Tstring =>
                             (if less_int (of_nat semiring_1_int (size_list l))
                                   (plus_inta
                                     (Pos (Bit0
    (Bit0 (Bit0 (Bit0 (Bit0 One))))))
                                     ix)
                               then Inr (decode_err
  [Chara (false, false, true, false, true, false, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, false, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, true, true, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, false, false, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, true, false, true, true, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, false, true, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false)]
  (ix, l))
                               else let
                                      val sz =
decode_uint (take (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))) la);
                                    in
                                      (if less_int
    (of_nat semiring_1_int (size_list l))
    (plus_inta (plus_inta sz (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))) ix)
then Inr (decode_err
           [Chara (false, true, true, false, false, false, true, false),
             Chara (true, false, true, false, false, true, true, false),
             Chara (true, true, true, false, true, true, true, false),
             Chara (true, false, true, false, false, true, true, false),
             Chara (false, true, false, false, true, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (false, true, false, false, false, true, true, false),
             Chara (true, false, false, true, true, true, true, false),
             Chara (false, false, true, false, true, true, true, false),
             Chara (true, false, true, false, false, true, true, false),
             Chara (true, true, false, false, true, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (false, true, false, false, true, true, true, false),
             Chara (true, false, true, false, false, true, true, false),
             Chara (true, false, true, true, false, true, true, false),
             Chara (true, false, false, false, false, true, true, false),
             Chara (true, false, false, true, false, true, true, false),
             Chara (false, true, true, true, false, true, true, false),
             Chara (true, false, false, true, false, true, true, false),
             Chara (false, true, true, true, false, true, true, false),
             Chara (true, true, true, false, false, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (false, false, true, false, true, true, true, false),
             Chara (false, false, false, true, false, true, true, false),
             Chara (true, false, false, false, false, true, true, false),
             Chara (false, true, true, true, false, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (true, true, false, false, true, true, true, false),
             Chara (false, false, true, false, true, true, true, false),
             Chara (false, true, false, false, true, true, true, false),
             Chara (true, false, false, true, false, true, true, false),
             Chara (false, true, true, true, false, true, true, false),
             Chara (true, true, true, false, false, true, true, false),
             Chara (false, false, false, false, false, true, false, false),
             Chara (true, true, false, false, true, true, true, false),
             Chara (true, false, false, true, false, true, true, false),
             Chara (false, true, false, true, true, true, true, false),
             Chara (true, false, true, false, false, true, true, false)]
           (ix, l))
else (if check_padding (nat sz)
           (drop (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))) la)
       then Inl (Vstring
                   (bytes_to_string
                     (take (nat sz)
                       (drop (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
                         la))),
                  plus_inta (of_nat semiring_1_int (skip_padding (nat sz)))
                    (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
       else Inr (decode_err
                  [Chara (true, false, false, true, false, false, true, false),
                    Chara (false, true, true, true, false, true, true, false),
                    Chara (false, true, true, false, true, true, true, false),
                    Chara (true, false, false, false, false, true, true, false),
                    Chara (false, false, true, true, false, true, true, false),
                    Chara (true, false, false, true, false, true, true, false),
                    Chara (false, false, true, false, false, true, true, false),
                    Chara (false, false, false, false, false, true, false,
                            false),
                    Chara (true, true, false, false, true, true, true, false),
                    Chara (false, false, true, false, true, true, true, false),
                    Chara (false, true, false, false, true, true, true, false),
                    Chara (true, false, false, true, false, true, true, false),
                    Chara (false, true, true, true, false, true, true, false),
                    Chara (true, true, true, false, false, true, true, false),
                    Chara (false, false, false, false, false, true, false,
                            false),
                    Chara (false, false, false, false, true, true, true, false),
                    Chara (true, false, false, false, false, true, true, false),
                    Chara (false, false, true, false, false, true, true, false),
                    Chara (false, false, true, false, false, true, true, false),
                    Chara (true, false, false, true, false, true, true, false),
                    Chara (false, true, true, true, false, true, true, false),
                    Chara (true, true, true, false, false, true, true, false)]
                  (ix, l))))
                                    end)
                           | Tarray ta =>
                             (if less_int (of_nat semiring_1_int (size_list l))
                                   (plus_inta
                                     (Pos (Bit0
    (Bit0 (Bit0 (Bit0 (Bit0 One))))))
                                     ix)
                               then Inr (decode_err
  [Chara (false, false, true, false, true, false, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, false, false, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, true, true, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, false, false, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, true, false, true, true, true, false, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (true, false, true, false, true, true, true, false),
    Chara (false, false, true, true, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, true, true, false, true, true, false),
    Chara (true, true, true, true, false, true, true, false),
    Chara (false, false, true, false, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, false, true, false, false, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (false, true, false, false, true, true, true, false),
    Chara (true, false, false, false, false, true, true, false),
    Chara (true, false, false, true, true, true, true, false),
    Chara (false, false, false, false, false, true, false, false),
    Chara (true, true, false, false, true, true, true, false),
    Chara (true, false, false, true, false, true, true, false),
    Chara (false, true, false, true, true, true, true, false),
    Chara (true, false, true, false, false, true, true, false)]
  (ix, l))
                               else let
                                      val n =
decode_uint (take (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))) la);
                                      val ts = replicate (nat n) ta;
                                    in
                                      (case
decode_dyn_tuple_heads ts Zero_int
  (plus_inta ix (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))), l)
of Inl (vos, (idxs, (byteoffset, bytes_parsed))) =>
  (case decode_dyn_tuple_tails idxs ts vos byteoffset
          (plus_inta ix (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))), l)
    of Inl (vs, bytes_parseda) =>
      Inl (Varray (ta, vs),
            plus_inta (plus_inta bytes_parsed bytes_parseda)
              (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
    | Inr a => Inr a)
| Inr a => Inr a)
                                    end)))
                end))
and decode_dyn_tuple_heads [] n (ix, l) = Inl ([], ([], (n, Zero_int)))
  | decode_dyn_tuple_heads (th :: tt) n (ix, l) =
    let
      val la = drop (nat (plus_inta ix n)) l;
    in
      (if abi_type_isstatic th
        then (case decodeb th (plus_inta ix n, l)
               of Inl (v, bytes_parsed) =>
                 (case decode_dyn_tuple_heads tt
                         (plus_inta n
                           (of_nat semiring_1_int (nat (abi_static_size th))))
                         (ix, l)
                   of Inl (vos, (idxs, (na, bytes_parseda))) =>
                     Inl (SOME v :: vos,
                           (NONE :: idxs,
                             (na, plus_inta bytes_parsed bytes_parseda)))
                   | Inr a => Inr a)
               | Inr a => Inr a)
        else (if less_nat (size_list la)
                   (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
               then Inr (decode_err
                          [Chara (false, false, true, false, true, false, true,
                                   false),
                            Chara (true, true, true, true, false, true, true,
                                    false),
                            Chara (true, true, true, true, false, true, true,
                                    false),
                            Chara (false, false, false, false, false, true,
                                    false, false),
                            Chara (false, true, true, false, false, true, true,
                                    false),
                            Chara (true, false, true, false, false, true, true,
                                    false),
                            Chara (true, true, true, false, true, true, true,
                                    false),
                            Chara (false, false, false, false, false, true,
                                    false, false),
                            Chara (false, true, false, false, false, true, true,
                                    false),
                            Chara (true, false, false, true, true, true, true,
                                    false),
                            Chara (false, false, true, false, true, true, true,
                                    false),
                            Chara (true, false, true, false, false, true, true,
                                    false),
                            Chara (true, true, false, false, true, true, true,
                                    false),
                            Chara (true, true, false, true, true, true, false,
                                    false),
                            Chara (false, false, false, false, false, true,
                                    false, false),
                            Chara (true, true, false, false, false, true, true,
                                    false),
                            Chara (true, true, true, true, false, true, true,
                                    false),
                            Chara (true, false, true, false, true, true, true,
                                    false),
                            Chara (false, false, true, true, false, true, true,
                                    false),
                            Chara (false, false, true, false, false, true, true,
                                    false),
                            Chara (false, false, false, false, false, true,
                                    false, false),
                            Chara (false, true, true, true, false, true, true,
                                    false),
                            Chara (true, true, true, true, false, true, true,
                                    false),
                            Chara (false, false, true, false, true, true, true,
                                    false),
                            Chara (false, false, false, false, false, true,
                                    false, false),
                            Chara (false, true, false, false, true, true, true,
                                    false),
                            Chara (true, false, true, false, false, true, true,
                                    false),
                            Chara (true, false, false, false, false, true, true,
                                    false),
                            Chara (false, false, true, false, false, true, true,
                                    false),
                            Chara (false, false, false, false, false, true,
                                    false, false),
                            Chara (false, false, true, false, true, true, true,
                                    false),
                            Chara (true, false, true, false, true, true, true,
                                    false),
                            Chara (false, false, false, false, true, true, true,
                                    false),
                            Chara (false, false, true, true, false, true, true,
                                    false),
                            Chara (true, false, true, false, false, true, true,
                                    false),
                            Chara (false, false, false, false, false, true,
                                    false, false),
                            Chara (false, false, false, true, false, true, true,
                                    false),
                            Chara (true, false, true, false, false, true, true,
                                    false),
                            Chara (true, false, false, false, false, true, true,
                                    false),
                            Chara (false, false, true, false, false, true, true,
                                    false)]
                          (ix, l))
               else let
                      val sz =
                        decode_sint
                          (take (nat_of_num
                                  (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
                            la);
                    in
                      (case decode_dyn_tuple_heads tt
                              (plus_inta n
                                (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
                              (ix, l)
                        of Inl (vos, (idxs, (na, bytes_parsed))) =>
                          Inl (NONE :: vos,
                                (SOME (plus_inta ix sz) :: idxs,
                                  (na, plus_inta bytes_parsed
 (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
                        | Inr a => Inr a)
                    end))
    end
and decode_dyn_tuple_tails [] [] [] uu (ix, l) = Inl ([], Zero_int)
  | decode_dyn_tuple_tails (NONE :: t) (th :: tt) (SOME vh :: vt) offset (ix, l)
    = (case decode_dyn_tuple_tails t tt vt offset (ix, l)
        of Inl (vs, bytes_parsed) => Inl (vh :: vs, bytes_parsed)
        | Inr a => Inr a)
  | decode_dyn_tuple_tails (SOME toffset :: t) (th :: tt) (NONE :: vt) offset
    (ix, l) =
    let
      val ixa = toffset;
    in
      (case decodeb th (ixa, l)
        of Inl (v, bytes_parsed) =>
          let
            val offseta = plus_inta offset bytes_parsed;
          in
            (case decode_dyn_tuple_tails t tt vt offseta (ix, l)
              of Inl (vs, bytes_parseda) =>
                Inl (v :: vs, plus_inta bytes_parsed bytes_parseda)
              | Inr a => Inr a)
          end
        | Inr a => Inr a)
    end
  | decode_dyn_tuple_tails (SOME vb :: va) [] ux uy (ix, l) =
    Inr (decode_err
          [Chara (true, true, false, false, true, false, true, false),
            Chara (false, false, false, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (false, false, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, true, false, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false)]
          (ix, l))
  | decode_dyn_tuple_tails (SOME vb :: va) uw [] uy (ix, l) =
    Inr (decode_err
          [Chara (true, true, false, false, true, false, true, false),
            Chara (false, false, false, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (false, false, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, true, false, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false)]
          (ix, l))
  | decode_dyn_tuple_tails (SOME vb :: va) uw (SOME vd :: vc) uy (ix, l) =
    Inr (decode_err
          [Chara (true, true, false, false, true, false, true, false),
            Chara (false, false, false, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (false, false, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, true, false, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false)]
          (ix, l))
  | decode_dyn_tuple_tails (v :: va) [] ux uy (ix, l) =
    Inr (decode_err
          [Chara (true, true, false, false, true, false, true, false),
            Chara (false, false, false, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (false, false, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, true, false, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false)]
          (ix, l))
  | decode_dyn_tuple_tails (v :: va) uw [] uy (ix, l) =
    Inr (decode_err
          [Chara (true, true, false, false, true, false, true, false),
            Chara (false, false, false, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (false, false, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, true, false, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false)]
          (ix, l))
  | decode_dyn_tuple_tails (NONE :: va) uw (NONE :: vc) uy (ix, l) =
    Inr (decode_err
          [Chara (true, true, false, false, true, false, true, false),
            Chara (false, false, false, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (false, false, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, true, false, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false)]
          (ix, l))
  | decode_dyn_tuple_tails [] (v :: va) ux uy (ix, l) =
    Inr (decode_err
          [Chara (true, true, false, false, true, false, true, false),
            Chara (false, false, false, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (false, false, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, true, false, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false)]
          (ix, l))
  | decode_dyn_tuple_tails uv (v :: va) [] uy (ix, l) =
    Inr (decode_err
          [Chara (true, true, false, false, true, false, true, false),
            Chara (false, false, false, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (false, false, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, true, false, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false)]
          (ix, l))
  | decode_dyn_tuple_tails [] uw (v :: va) uy (ix, l) =
    Inr (decode_err
          [Chara (true, true, false, false, true, false, true, false),
            Chara (false, false, false, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (false, false, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, true, false, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false)]
          (ix, l))
  | decode_dyn_tuple_tails uv [] (v :: va) uy (ix, l) =
    Inr (decode_err
          [Chara (true, true, false, false, true, false, true, false),
            Chara (false, false, false, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (false, false, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, true, false, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, false, true, false, false, true, true, false),
            Chara (true, false, true, false, false, true, true, false)]
          (ix, l));

fun decodea t l =
  (if abi_type_valid t
    then (case decodeb t (Zero_int, l) of Inl (v, _) => Inl v | Inr a => Inr a)
    else Inr [Chara (true, false, false, true, false, false, true, false),
               Chara (false, true, true, true, false, true, true, false),
               Chara (false, true, true, false, true, true, true, false),
               Chara (true, false, false, false, false, true, true, false),
               Chara (false, false, true, true, false, true, true, false),
               Chara (true, false, false, true, false, true, true, false),
               Chara (false, false, true, false, false, true, true, false),
               Chara (false, false, false, false, false, true, false, false),
               Chara (true, false, false, false, false, false, true, false),
               Chara (false, true, false, false, false, false, true, false),
               Chara (true, false, false, true, false, false, true, false),
               Chara (false, false, false, false, false, true, false, false),
               Chara (false, false, true, false, true, true, true, false),
               Chara (true, false, false, true, true, true, true, false),
               Chara (false, false, false, false, true, true, true, false),
               Chara (true, false, true, false, false, true, true, false)]);

fun integer_of_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (of_bool
                        zero_neq_one_integer
                        b7, (2 : IntInf.int)), of_bool zero_neq_one_integer
         b6), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                   b5), (2 : IntInf.int)), of_bool
                     zero_neq_one_integer
                     b4), (2 : IntInf.int)), of_bool zero_neq_one_integer
       b3), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                 b2), (2 : IntInf.int)), of_bool
                   zero_neq_one_integer
                   b1), (2 : IntInf.int)), of_bool zero_neq_one_integer b0);

fun implode cs =
  (String.implode
    o List.map (fn k => if 0 <= k andalso k < 128 then (Char.chr o IntInf.toInt) k else raise Fail "Non-ASCII character in literal"))
    (map integer_of_char cs);

fun decode x =
  (fn typea => fn encoding =>
    (case parseType (explode typea)
      of NONE =>
        implode
          [Chara (true, false, true, false, false, false, true, false),
            Chara (false, true, false, false, true, false, true, false),
            Chara (false, true, false, false, true, false, true, false),
            Chara (false, true, false, true, true, true, false, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, false, false, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, false, true, false, true, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, false, false, true, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (true, true, false, false, true, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, true, true, true, false),
            Chara (true, false, false, true, true, true, true, false),
            Chara (false, false, false, false, true, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, true, true, true, false, true, false, false)]
      | SOME typeb =>
        (case parseWordsPrefixed (explode encoding)
          of NONE =>
            implode
              [Chara (true, false, true, false, false, false, true, false),
                Chara (false, true, false, false, true, false, true, false),
                Chara (false, true, false, false, true, false, true, false),
                Chara (false, true, false, true, true, true, false, false),
                Chara (false, false, false, false, false, true, false, false),
                Chara (true, true, false, false, false, false, true, false),
                Chara (true, false, false, false, false, true, true, false),
                Chara (false, true, true, true, false, true, true, false),
                Chara (false, true, true, true, false, true, true, false),
                Chara (true, true, true, true, false, true, true, false),
                Chara (false, false, true, false, true, true, true, false),
                Chara (false, false, false, false, false, true, false, false),
                Chara (false, false, false, false, true, true, true, false),
                Chara (true, false, false, false, false, true, true, false),
                Chara (false, true, false, false, true, true, true, false),
                Chara (true, true, false, false, true, true, true, false),
                Chara (true, false, true, false, false, true, true, false),
                Chara (false, false, false, false, false, true, false, false),
                Chara (true, false, true, false, false, true, true, false),
                Chara (false, true, true, true, false, true, true, false),
                Chara (true, true, false, false, false, true, true, false),
                Chara (true, true, true, true, false, true, true, false),
                Chara (false, false, true, false, false, true, true, false),
                Chara (true, false, false, true, false, true, true, false),
                Chara (false, true, true, true, false, true, true, false),
                Chara (true, true, true, false, false, true, true, false),
                Chara (false, true, true, true, false, true, false, false)]
          | SOME encodinga =>
            (case decodea typeb encodinga
              of Inl value =>
                implode
                  ([Chara (true, true, true, true, false, false, true, false),
                     Chara (true, true, false, true, false, false, true, false),
                     Chara (false, true, false, true, true, true, false, false),
                     Chara (false, false, false, false, false, true, false,
                             false)] @
                    writeValue value)
              | Inr msg =>
                implode
                  ([Chara (true, false, true, false, false, false, true, false),
                     Chara (false, true, false, false, true, false, true,
                             false),
                     Chara (false, true, false, false, true, false, true,
                             false),
                     Chara (false, true, false, true, true, true, false, false),
                     Chara (false, false, false, false, false, true, false,
                             false)] @
                    msg)))))
    x;

fun splitFunction
  (Chara (false, true, false, true, true, true, false, false) :: tail) [] = NONE
  | splitFunction
    (Chara (false, true, false, true, true, true, false, false) :: tail)
    (p :: partial) =
    (if null tail then NONE else SOME (rev (p :: partial), tail))
  | splitFunction (Chara (true, va, vb, vc, vd, ve, vf, vg) :: tail) partial =
    splitFunction tail (Chara (true, va, vb, vc, vd, ve, vf, vg) :: partial)
  | splitFunction (Chara (v, false, vb, vc, vd, ve, vf, vg) :: tail) partial =
    splitFunction tail (Chara (v, false, vb, vc, vd, ve, vf, vg) :: partial)
  | splitFunction (Chara (v, va, true, vc, vd, ve, vf, vg) :: tail) partial =
    splitFunction tail (Chara (v, va, true, vc, vd, ve, vf, vg) :: partial)
  | splitFunction (Chara (v, va, vb, false, vd, ve, vf, vg) :: tail) partial =
    splitFunction tail (Chara (v, va, vb, false, vd, ve, vf, vg) :: partial)
  | splitFunction (Chara (v, va, vb, vc, false, ve, vf, vg) :: tail) partial =
    splitFunction tail (Chara (v, va, vb, vc, false, ve, vf, vg) :: partial)
  | splitFunction (Chara (v, va, vb, vc, vd, false, vf, vg) :: tail) partial =
    splitFunction tail (Chara (v, va, vb, vc, vd, false, vf, vg) :: partial)
  | splitFunction (Chara (v, va, vb, vc, vd, ve, true, vg) :: tail) partial =
    splitFunction tail (Chara (v, va, vb, vc, vd, ve, true, vg) :: partial)
  | splitFunction (Chara (v, va, vb, vc, vd, ve, vf, true) :: tail) partial =
    splitFunction tail (Chara (v, va, vb, vc, vd, ve, vf, true) :: partial)
  | splitFunction [] uu = NONE;

fun parseU32 x =
  (fn str =>
    (case parseWords str of NONE => NONE
      | SOME w =>
        (if equal_nat (size_list w) (nat_of_num (Bit0 (Bit0 One)))
          then SOME (word_rcat (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                      (len0_bit0
                        (len0_bit0
                          (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
                      w)
          else NONE)))
    x;

fun parseSelector x =
  (fn a =>
    (case a of [] => NONE | Chara (true, _, _, _, _, _, _, _) :: _ => NONE
      | Chara (false, true, _, _, _, _, _, _) :: _ => NONE
      | Chara (false, false, true, _, _, _, _, _) :: _ => NONE
      | Chara (false, false, false, true, _, _, _, _) :: _ => NONE
      | Chara (false, false, false, false, true, true, true, _) :: _ => NONE
      | Chara (false, false, false, false, true, true, false, true) :: _ => NONE
      | [Chara (false, false, false, false, true, true, false, false)] => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (true, _, _, _, _, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, true, _, _, _, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, true, _, _, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, true, true, true, true) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, true, true, true, false) :: hexstr
        => map_option
             (uint (len0_bit0
                     (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))))
             (parseU32 hexstr)
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, true, true, false, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, true, false, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, false, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, false, _, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, false, _, _) :: _ => NONE
      | Chara (false, false, false, false, false, _, _, _) :: _ => NONE))
    x;

fun parseU160 x =
  (fn str =>
    (case parseWords str of NONE => NONE
      | SOME w =>
        (if equal_nat (size_list w) (nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 One)))))
          then SOME (word_rcat (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                      (len0_bit0
                        (len0_bit0
                          (len0_bit0
                            (len0_bit0
                              (len0_bit0 (len0_bit1 (len0_bit0 len0_num1)))))))
                      w)
          else NONE)))
    x;

fun parseAddress x =
  (fn a =>
    (case a of [] => NONE | Chara (true, _, _, _, _, _, _, _) :: _ => NONE
      | Chara (false, true, _, _, _, _, _, _) :: _ => NONE
      | Chara (false, false, true, _, _, _, _, _) :: _ => NONE
      | Chara (false, false, false, true, _, _, _, _) :: _ => NONE
      | Chara (false, false, false, false, true, true, true, _) :: _ => NONE
      | Chara (false, false, false, false, true, true, false, true) :: _ => NONE
      | [Chara (false, false, false, false, true, true, false, false)] => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (true, _, _, _, _, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, true, _, _, _, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, true, _, _, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, true, true, true, true) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, true, true, true, false) :: hexstr
        => map_option
             (uint (len0_bit0
                     (len0_bit0
                       (len0_bit0
                         (len0_bit0
                           (len0_bit0 (len0_bit1 (len0_bit0 len0_num1))))))))
             (parseU160 hexstr)
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, true, true, false, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, true, false, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, true, false, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, true, false, false) ::
          Chara (false, false, false, false, _, _, _, _) :: _
        => NONE
      | Chara (false, false, false, false, true, false, _, _) :: _ => NONE
      | Chara (false, false, false, false, false, _, _, _) :: _ => NONE))
    x;

fun parseUint x =
  (fn str => map_option (of_nat semiring_1_int) (parseNat str)) x;

fun parseSint
  (Chara (true, false, true, true, false, true, false, false) :: tail) =
  map_option (fn n => uminus_int (of_nat semiring_1_int n)) (parseNat tail)
  | parseSint [] = map_option (of_nat semiring_1_int) (parseNat [])
  | parseSint (Chara (false, vc, vd, ve, vf, vg, vh, vi) :: va) =
    map_option (of_nat semiring_1_int)
      (parseNat (Chara (false, vc, vd, ve, vf, vg, vh, vi) :: va))
  | parseSint (Chara (vb, true, vd, ve, vf, vg, vh, vi) :: va) =
    map_option (of_nat semiring_1_int)
      (parseNat (Chara (vb, true, vd, ve, vf, vg, vh, vi) :: va))
  | parseSint (Chara (vb, vc, false, ve, vf, vg, vh, vi) :: va) =
    map_option (of_nat semiring_1_int)
      (parseNat (Chara (vb, vc, false, ve, vf, vg, vh, vi) :: va))
  | parseSint (Chara (vb, vc, vd, false, vf, vg, vh, vi) :: va) =
    map_option (of_nat semiring_1_int)
      (parseNat (Chara (vb, vc, vd, false, vf, vg, vh, vi) :: va))
  | parseSint (Chara (vb, vc, vd, ve, true, vg, vh, vi) :: va) =
    map_option (of_nat semiring_1_int)
      (parseNat (Chara (vb, vc, vd, ve, true, vg, vh, vi) :: va))
  | parseSint (Chara (vb, vc, vd, ve, vf, false, vh, vi) :: va) =
    map_option (of_nat semiring_1_int)
      (parseNat (Chara (vb, vc, vd, ve, vf, false, vh, vi) :: va))
  | parseSint (Chara (vb, vc, vd, ve, vf, vg, true, vi) :: va) =
    map_option (of_nat semiring_1_int)
      (parseNat (Chara (vb, vc, vd, ve, vf, vg, true, vi) :: va))
  | parseSint (Chara (vb, vc, vd, ve, vf, vg, vh, true) :: va) =
    map_option (of_nat semiring_1_int)
      (parseNat (Chara (vb, vc, vd, ve, vf, vg, vh, true) :: va));

fun typedValueParser (Tuint n) (PrimaryValue v) =
  map_option (fn a => Vuint (n, a)) (parseUint v)
  | typedValueParser (Tsint n) (PrimaryValue v) =
    map_option (fn a => Vsint (n, a)) (parseSint v)
  | typedValueParser Taddr (PrimaryValue v) = map_option Vaddr (parseAddress v)
  | typedValueParser Tbool (PrimaryValue v) =
    (if equal_lista equal_char v
          [Chara (false, false, true, false, true, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (true, false, true, false, true, true, true, false),
            Chara (true, false, true, false, false, true, true, false)]
      then SOME (Vbool true)
      else (if equal_lista equal_char v
                 [Chara (false, true, true, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (true, true, false, false, true, true, true, false),
                   Chara (true, false, true, false, false, true, true, false)]
             then SOME (Vbool false) else NONE))
  | typedValueParser (Tfbytes n) (PrimaryValue v) =
    bind (parseWordsPrefixed v)
      (fn ws =>
        (if equal_nat (size_list ws) n then SOME (Vfbytes (n, ws)) else NONE))
  | typedValueParser Tfunction (PrimaryValue v) =
    bind (splitFunction v [])
      (fn (x, y) =>
        (case (parseAddress x, parseSelector y) of (NONE, _) => NONE
          | (SOME _, NONE) => NONE
          | (SOME addr, SOME sel) => SOME (Vfunction (addr, sel))))
  | typedValueParser (Tfarray (t, n)) (ArrayValue vs) =
    (if equal_nat (size_list vs) n
      then map_option (fn a => Vfarray (t, n, a))
             (those (map (typedValueParser t) vs))
      else NONE)
  | typedValueParser (Ttuple ts) (TupleValue vs) =
    (if equal_nat (size_list vs) (size_list ts)
      then map_option (fn a => Vtuple (ts, a))
             (those (map (fn (a, b) => typedValueParser a b) (zip ts vs)))
      else NONE)
  | typedValueParser Tbytes (PrimaryValue v) =
    map_option Vbytes (parseWordsPrefixed v)
  | typedValueParser Tstring (PrimaryValue v) =
    map_option Vstring
      (map_option
        (map (fn x =>
               char_of
                 (equal_int, unique_euclidean_semiring_with_bit_shifts_int)
                 (uint (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) x)))
        (parseWordsPrefixed v))
  | typedValueParser (Tarray t) (ArrayValue vs) =
    map_option (fn a => Varray (t, a)) (those (map (typedValueParser t) vs))
  | typedValueParser (Tsint v) (ArrayValue va) = NONE
  | typedValueParser (Tsint v) (TupleValue va) = NONE
  | typedValueParser Taddr (ArrayValue v) = NONE
  | typedValueParser Taddr (TupleValue v) = NONE
  | typedValueParser Tbool (ArrayValue v) = NONE
  | typedValueParser Tbool (TupleValue v) = NONE
  | typedValueParser (Tfixed (v, va)) uv = NONE
  | typedValueParser (Tufixed (v, va)) uv = NONE
  | typedValueParser (Tfbytes v) (ArrayValue va) = NONE
  | typedValueParser (Tfbytes v) (TupleValue va) = NONE
  | typedValueParser Tfunction (ArrayValue v) = NONE
  | typedValueParser Tfunction (TupleValue v) = NONE
  | typedValueParser (Tfarray (v, va)) (TupleValue vb) = NONE
  | typedValueParser (Tfarray (v, va)) (PrimaryValue vb) = NONE
  | typedValueParser (Ttuple v) (ArrayValue va) = NONE
  | typedValueParser (Ttuple v) (PrimaryValue va) = NONE
  | typedValueParser Tbytes (ArrayValue v) = NONE
  | typedValueParser Tbytes (TupleValue v) = NONE
  | typedValueParser Tstring (ArrayValue v) = NONE
  | typedValueParser Tstring (TupleValue v) = NONE
  | typedValueParser (Tarray v) (TupleValue va) = NONE
  | typedValueParser (Tarray v) (PrimaryValue va) = NONE
  | typedValueParser (Tuint va) (ArrayValue v) = NONE
  | typedValueParser (Tuint va) (TupleValue v) = NONE;

fun valueParser [Elem x] [] = SOME (PrimaryValue x)
  | valueParser (Elem x :: tail) (VPS_arrtuple (w, ar) :: st) =
    valueParser tail
      (VPS_primary (PrimaryValue x) :: VPS_arrtuple (w, ar) :: st)
  | valueParser (LBrack :: tail) st =
    valueParser tail (VPS_arrtuple (false, []) :: st)
  | valueParser (LParen :: tail) st =
    valueParser tail (VPS_arrtuple (true, []) :: st)
  | valueParser (RBrack :: tail) (VPS_arrtuple (false, arr) :: st) =
    valueParser tail (VPS_primary (ArrayValue []) :: st)
  | valueParser (RBrack :: tail)
    (VPS_primary x :: VPS_arrtuple (false, arr) :: st) =
    valueParser tail (VPS_primary (ArrayValue (rev (x :: arr))) :: st)
  | valueParser (RParen :: tail)
    (VPS_primary x :: VPS_arrtuple (true, arr) :: st) =
    valueParser tail (VPS_primary (TupleValue (rev (x :: arr))) :: st)
  | valueParser (Comma :: tail) (VPS_primary x :: VPS_arrtuple (w, arr) :: st) =
    valueParser tail (VPS_arrtuple (w, x :: arr) :: st)
  | valueParser [] [VPS_primary y] = SOME y
  | valueParser [] [] = NONE
  | valueParser [] (VPS_arrtuple (vb, vc) :: va) = NONE
  | valueParser [] (v :: vb :: vc) = NONE
  | valueParser (RParen :: va) [] = NONE
  | valueParser (RParen :: va) (VPS_arrtuple (vc, vd) :: vb) = NONE
  | valueParser (RParen :: va) [v] = NONE
  | valueParser (RParen :: va) (v :: VPS_primary ve :: vd) = NONE
  | valueParser (RParen :: va) (v :: VPS_arrtuple (false, vf) :: vd) = NONE
  | valueParser (RBrack :: va) [] = NONE
  | valueParser (RBrack :: va) [VPS_primary vc] = NONE
  | valueParser (RBrack :: va) (VPS_primary vc :: VPS_primary ve :: vd) = NONE
  | valueParser (RBrack :: va) (VPS_primary vc :: VPS_arrtuple (true, vf) :: vd)
    = NONE
  | valueParser (RBrack :: va) (VPS_arrtuple (true, vd) :: vb) = NONE
  | valueParser (Comma :: va) [] = NONE
  | valueParser (Comma :: va) (VPS_arrtuple (vc, vd) :: vb) = NONE
  | valueParser (Comma :: va) [v] = NONE
  | valueParser (Comma :: va) (v :: VPS_primary ve :: vd) = NONE
  | valueParser (Elem va :: vb :: vc) [] = NONE
  | valueParser (Elem va :: vb :: vc) (VPS_primary ve :: vd) = NONE
  | valueParser (Elem vd :: vc) (VPS_primary vb :: va) = NONE;

fun parseTypedValue x =
  (fn typea => fn str =>
    bind (valueParser (scanTokens str) []) (typedValueParser typea))
    x;

fun array_value_valid_aux t l =
  uint_value_valid
    (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
    (of_nat semiring_1_int (size_list l)) andalso
    list_all (fn v => equal_abi_typea (abi_get_type v) t) l;

fun string_value_valid s =
  uint_value_valid
    (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
    (of_nat semiring_1_int (size_list s));

fun bytes_value_valid bs =
  uint_value_valid
    (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
    (of_nat semiring_1_int (size_list bs));

fun bool_value_valid b = true;

fun abi_value_valid_aux (Vuint (n, i)) = uint_value_valid n i
  | abi_value_valid_aux (Vsint (n, i)) = sint_value_valid n i
  | abi_value_valid_aux (Vaddr i) = addr_value_valid i
  | abi_value_valid_aux (Vbool b) = bool_value_valid b
  | abi_value_valid_aux (Vfixed (m, n, r)) = fixed_value_valid m n r
  | abi_value_valid_aux (Vufixed (m, n, r)) = ufixed_value_valid m n r
  | abi_value_valid_aux (Vfbytes (n, l)) = fbytes_value_valid n l
  | abi_value_valid_aux (Vfunction (i1, i2)) = function_value_valid i1 i2
  | abi_value_valid_aux (Vfarray (t, n, l)) =
    farray_value_valid_aux t n l andalso list_all abi_value_valid_aux l
  | abi_value_valid_aux (Vtuple (ts, vs)) =
    tuple_value_valid_aux ts vs andalso list_all abi_value_valid_aux vs
  | abi_value_valid_aux (Vbytes bs) = bytes_value_valid bs
  | abi_value_valid_aux (Vstring s) = string_value_valid s
  | abi_value_valid_aux (Varray (t, l)) =
    array_value_valid_aux t l andalso list_all abi_value_valid_aux l;

fun abi_value_valid v =
  abi_type_valid (abi_get_type v) andalso abi_value_valid_aux v;

fun encode_int i =
  word_rsplit
    (len0_bit0
      (len0_bit0
        (len0_bit0
          (len0_bit0
            (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))))))
    (len_bit0 (len_bit0 (len_bit0 len_num1)))
    (word_of_int
      (len0_bit0
        (len0_bit0
          (len0_bit0
            (len0_bit0
              (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))))))
      i);

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k)
                  then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                  else let
                         val (r, s) =
                           IntInf.divMod (IntInf.abs k, IntInf.abs l);
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                           else let
                                  val (r, s) =
                                    IntInf.divMod (IntInf.abs k, IntInf.abs l);
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun int_of_integer k =
  (if IntInf.< (k, (0 : IntInf.int))
    then uminus_int (int_of_integer (IntInf.~ k))
    else (if ((k : IntInf.int) = (0 : IntInf.int)) then Zero_int
           else let
                  val (l, j) = divmod_integer k (2 : IntInf.int);
                  val la = times_inta (Pos (Bit0 One)) (int_of_integer l);
                in
                  (if ((j : IntInf.int) = (0 : IntInf.int)) then la
                    else plus_inta la one_inta)
                end));

fun string_to_bytes s =
  map (fn c =>
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (int_of_integer (integer_of_char c)))
    s;

fun pad_bytes l =
  (case divmod_nat (size_list l)
          (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
    of (_, Zero_nat) => l
    | (_, Suc rem) =>
      l @ replicate
            (minus_nat (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
              (Suc rem))
            (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
              Zero_int));

fun encode_function_sel addr sel =
  pad_bytes
    (word_rsplit
       (len0_bit0
         (len0_bit0
           (len0_bit0
             (len0_bit0 (len0_bit0 (len0_bit1 (len0_bit0 len0_num1)))))))
       (len_bit0 (len_bit0 (len_bit0 len_num1)))
       (word_of_int
         (len0_bit0
           (len0_bit0
             (len0_bit0
               (len0_bit0 (len0_bit0 (len0_bit1 (len0_bit0 len0_num1)))))))
         addr) @
      word_rsplit
        (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
        (len_bit0 (len_bit0 (len_bit0 len_num1)))
        (word_of_int
          (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
          sel));

fun encode_fbytes n l = pad_bytes (take n l);

fun encode_fixed n r =
  encode_int
    (fst (quotient_of
           (times_rata r
             (power power_rat (of_int (Pos (Bit0 (Bit1 (Bit0 One))))) n))));

fun encode_bool true = encode_int one_inta
  | encode_bool false = encode_int Zero_int;

fun encode_static (Vuint (n, i)) = Inl (encode_int i)
  | encode_static (Vsint (n, i)) = Inl (encode_int i)
  | encode_static (Vaddr a) = Inl (encode_int a)
  | encode_static (Vbool b) = Inl (encode_bool b)
  | encode_static (Vfixed (m, n, r)) = Inl (encode_fixed n r)
  | encode_static (Vufixed (m, n, r)) = Inl (encode_fixed n r)
  | encode_static (Vfbytes (n, l)) = Inl (encode_fbytes n l)
  | encode_static (Vfunction (addr, sel)) = Inl (encode_function_sel addr sel)
  | encode_static (Vfarray (t, n, l)) =
    (case those_err (map encode_static l) of Inl bs => Inl (concat bs)
      | Inr a => Inr a)
  | encode_static (Vtuple (ts, vs)) =
    (case those_err (map encode_static vs) of Inl bs => Inl (concat bs)
      | Inr a => Inr a)
  | encode_static (Vbytes v) =
    Inr [Chara (true, true, false, false, false, false, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, true, false, false, true, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, false, true, true, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (true, false, true, true, false, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, true, true, false, true, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (true, false, true, false, true, true, true, false),
          Chara (true, false, true, false, false, true, true, false)]
  | encode_static (Vstring v) =
    Inr [Chara (true, true, false, false, false, false, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, true, false, false, true, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, false, true, true, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (true, false, true, true, false, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, true, true, false, true, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (true, false, true, false, true, true, true, false),
          Chara (true, false, true, false, false, true, true, false)]
  | encode_static (Varray (v, va)) =
    Inr [Chara (true, true, false, false, false, false, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, true, false, false, true, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, false, true, true, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (true, false, true, true, false, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, true, true, false, true, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (true, false, true, false, true, true, true, false),
          Chara (true, false, true, false, false, true, true, false)];

fun heads_length [] = Zero_int
  | heads_length (h :: t) =
    let
      val tyh = abi_get_type h;
    in
      (if abi_type_isstatic tyh
        then plus_inta (abi_static_size tyh) (heads_length t)
        else plus_inta (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
               (heads_length t))
    end;

fun encodeb v =
  (if abi_type_isstatic (abi_get_type v) then encode_static v
    else (case v
           of Vuint (_, _) =>
             Inr [Chara (true, true, false, false, true, false, true, false),
                   Chara (false, false, false, true, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (true, false, true, false, true, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, true, false, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, false, true, false, true, false, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, true, true, true, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, true, true, false, false, true, false, false),
                   Chara (true, false, false, true, false, true, false, false)]
           | Vsint (_, _) =>
             Inr [Chara (true, true, false, false, true, false, true, false),
                   Chara (false, false, false, true, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (true, false, true, false, true, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, true, false, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, false, true, false, true, false, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, true, true, true, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, true, true, false, false, true, false, false),
                   Chara (true, false, false, true, false, true, false, false)]
           | Vaddr _ =>
             Inr [Chara (true, true, false, false, true, false, true, false),
                   Chara (false, false, false, true, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (true, false, true, false, true, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, true, false, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, false, true, false, true, false, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, true, true, true, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, true, true, false, false, true, false, false),
                   Chara (true, false, false, true, false, true, false, false)]
           | Vbool _ =>
             Inr [Chara (true, true, false, false, true, false, true, false),
                   Chara (false, false, false, true, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (true, false, true, false, true, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, true, false, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, false, true, false, true, false, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, true, true, true, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, true, true, false, false, true, false, false),
                   Chara (true, false, false, true, false, true, false, false)]
           | Vfixed (_, _, _) =>
             Inr [Chara (true, true, false, false, true, false, true, false),
                   Chara (false, false, false, true, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (true, false, true, false, true, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, true, false, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, false, true, false, true, false, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, true, true, true, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, true, true, false, false, true, false, false),
                   Chara (true, false, false, true, false, true, false, false)]
           | Vufixed (_, _, _) =>
             Inr [Chara (true, true, false, false, true, false, true, false),
                   Chara (false, false, false, true, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (true, false, true, false, true, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, true, false, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, false, true, false, true, false, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, true, true, true, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, true, true, false, false, true, false, false),
                   Chara (true, false, false, true, false, true, false, false)]
           | Vfbytes (_, _) =>
             Inr [Chara (true, true, false, false, true, false, true, false),
                   Chara (false, false, false, true, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (true, false, true, false, true, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, true, false, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, false, true, false, true, false, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, true, true, true, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, true, true, false, false, true, false, false),
                   Chara (true, false, false, true, false, true, false, false)]
           | Vfunction (_, _) =>
             Inr [Chara (true, true, false, false, true, false, true, false),
                   Chara (false, false, false, true, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (true, false, true, false, true, true, true, false),
                   Chara (false, false, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, true, false, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, false, false, false, false, true, false,
                           false),
                   Chara (false, false, false, true, false, true, false, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (false, true, true, true, false, true, true, false),
                   Chara (true, true, false, false, false, true, true, false),
                   Chara (true, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, false, true, true, false),
                   Chara (true, false, true, false, false, true, true, false),
                   Chara (true, true, true, false, false, true, false, false),
                   Chara (true, false, false, true, false, true, false, false)]
           | Vfarray (_, _, vs) =>
             (case encode_tuple_tails vs Zero_int (heads_length vs)
               of Inl bvs =>
                 (case encode_tuple_heads vs bvs
                   of Inl (heads, tails) => Inl (heads @ tails)
                   | Inr a => Inr a)
               | Inr a => Inr a)
           | Vtuple (_, vs) =>
             (case encode_tuple_tails vs Zero_int (heads_length vs)
               of Inl bvs =>
                 (case encode_tuple_heads vs bvs
                   of Inl (heads, tails) => Inl (heads @ tails)
                   | Inr a => Inr a)
               | Inr a => Inr a)
           | Vbytes l =>
             Inl (encode_int (of_nat semiring_1_int (size_list l)) @
                   pad_bytes l)
           | Vstring s =>
             let
               val bs = string_to_bytes s;
             in
               Inl (encode_int (of_nat semiring_1_int (size_list bs)) @
                     pad_bytes bs)
             end
           | Varray (_, vs) =>
             (case encode_tuple_tails vs Zero_int (heads_length vs)
               of Inl bvs =>
                 (case encode_tuple_heads vs bvs
                   of Inl (heads, tails) =>
                     Inl (encode_int (of_nat semiring_1_int (size_list vs)) @
                           heads @ tails)
                   | Inr a => Inr a)
               | Inr a => Inr a)))
and encode_tuple_heads [] [] = Inl ([], [])
  | encode_tuple_heads (v :: vs) ((offset, bs) :: bss) =
    (if abi_type_isstatic (abi_get_type v)
      then (case encodeb v
             of Inl head1 =>
               (case encode_tuple_heads vs bss
                 of Inl (heads, tails) => Inl (head1 @ heads, bs @ tails)
                 | Inr a => Inr a)
             | Inr a => Inr a)
      else (case encode_tuple_heads vs bss
             of Inl (heads, tails) =>
               Inl (encode_int offset @ heads, bs @ tails)
             | Inr a => Inr a))
  | encode_tuple_heads (v :: va) [] =
    Inr [Chara (true, true, false, false, true, false, true, false),
          Chara (false, false, false, true, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (true, false, true, false, true, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, true, false, false, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, false, false, true, false, true, false, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, true, true, false, false, true, false, false),
          Chara (true, true, true, true, true, false, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, true, false, true, true, true, false),
          Chara (false, false, false, false, true, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, true, true, true, true, false, true, false),
          Chara (false, false, false, true, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (true, false, false, true, false, true, false, false)]
  | encode_tuple_heads [] (v :: va) =
    Inr [Chara (true, true, false, false, true, false, true, false),
          Chara (false, false, false, true, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (true, false, true, false, true, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, true, false, false, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, false, false, false, false, true, false, false),
          Chara (false, false, false, true, false, true, false, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, true, true, false, false, true, false, false),
          Chara (true, true, true, true, true, false, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, true, false, true, true, true, false),
          Chara (false, false, false, false, true, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, true, true, true, true, false, true, false),
          Chara (false, false, false, true, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (true, false, false, true, false, true, false, false)]
and encode_tuple_tails [] uw ux = Inl []
  | encode_tuple_tails (v :: rest) headlen len_total =
    (if abi_type_isstatic (abi_get_type v)
      then (case encode_tuple_tails rest headlen len_total
             of Inl ts => Inl ((plus_inta len_total headlen, []) :: ts)
             | Inr a => Inr a)
      else (case encodeb v
             of Inl enc =>
               let
                 val len_totala =
                   plus_inta len_total (of_nat semiring_1_int (size_list enc));
               in
                 (case encode_tuple_tails rest headlen len_totala
                   of Inl ts =>
                     (if sint_value_valid
                           (nat_of_num
                             (Bit0 (Bit0 (Bit0
   (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
                           (plus_inta len_total headlen)
                       then Inl ((plus_inta len_total headlen, enc) :: ts)
                       else Inr [Chara (true, false, true, false, false, false,
 true, false),
                                  Chara (false, true, true, true, false, true,
  true, false),
                                  Chara (true, true, false, false, false, true,
  true, false),
                                  Chara (true, true, true, true, false, true,
  true, false),
                                  Chara (false, false, true, false, false, true,
  true, false),
                                  Chara (true, false, true, false, false, true,
  true, false),
                                  Chara (false, false, true, false, false, true,
  true, false),
                                  Chara (false, false, false, false, false,
  true, false, false),
                                  Chara (false, true, true, false, true, true,
  true, false),
                                  Chara (true, false, false, false, false, true,
  true, false),
                                  Chara (false, false, true, true, false, true,
  true, false),
                                  Chara (true, false, true, false, true, true,
  true, false),
                                  Chara (true, false, true, false, false, true,
  true, false),
                                  Chara (false, false, false, false, false,
  true, false, false),
                                  Chara (true, false, false, true, false, true,
  true, false),
                                  Chara (true, true, false, false, true, true,
  true, false),
                                  Chara (false, false, false, false, false,
  true, false, false),
                                  Chara (false, false, true, false, true, true,
  true, false),
                                  Chara (true, true, true, true, false, true,
  true, false),
                                  Chara (true, true, true, true, false, true,
  true, false),
                                  Chara (false, false, false, false, false,
  true, false, false),
                                  Chara (false, false, true, true, false, true,
  true, false),
                                  Chara (true, true, true, true, false, true,
  true, false),
                                  Chara (false, true, true, true, false, true,
  true, false),
                                  Chara (true, true, true, false, false, true,
  true, false)])
                   | Inr a => Inr a)
               end
             | Inr a => Inr a));

fun encodea v =
  (if abi_value_valid v then encodeb v
    else Inr [Chara (true, false, false, true, false, false, true, false),
               Chara (false, true, true, true, false, true, true, false),
               Chara (false, true, true, false, true, true, true, false),
               Chara (true, false, false, false, false, true, true, false),
               Chara (false, false, true, true, false, true, true, false),
               Chara (true, false, false, true, false, true, true, false),
               Chara (false, false, true, false, false, true, true, false),
               Chara (false, false, false, false, false, true, false, false),
               Chara (true, false, false, false, false, false, true, false),
               Chara (false, true, false, false, false, false, true, false),
               Chara (true, false, false, true, false, false, true, false),
               Chara (false, false, false, false, false, true, false, false),
               Chara (false, true, true, false, true, true, true, false),
               Chara (true, false, false, false, false, true, true, false),
               Chara (false, false, true, true, false, true, true, false),
               Chara (true, false, true, false, true, true, true, false),
               Chara (true, false, true, false, false, true, true, false)]);

fun encode x =
  (fn typea => fn value =>
    (case parseType (explode typea)
      of NONE =>
        implode
          [Chara (true, false, true, false, false, false, true, false),
            Chara (false, true, false, false, true, false, true, false),
            Chara (false, true, false, false, true, false, true, false),
            Chara (false, true, false, true, true, true, false, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (true, true, false, false, false, false, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (false, true, true, true, false, true, true, false),
            Chara (true, true, true, true, false, true, true, false),
            Chara (false, false, true, false, true, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, false, false, true, true, true, false),
            Chara (true, false, false, false, false, true, true, false),
            Chara (false, true, false, false, true, true, true, false),
            Chara (true, true, false, false, true, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, false, false, false, false, true, false, false),
            Chara (false, false, true, false, true, true, true, false),
            Chara (true, false, false, true, true, true, true, false),
            Chara (false, false, false, false, true, true, true, false),
            Chara (true, false, true, false, false, true, true, false),
            Chara (false, true, true, true, false, true, false, false)]
      | SOME typeb =>
        (case parseTypedValue typeb (explode value)
          of NONE =>
            implode
              [Chara (true, false, true, false, false, false, true, false),
                Chara (false, true, false, false, true, false, true, false),
                Chara (false, true, false, false, true, false, true, false),
                Chara (false, true, false, true, true, true, false, false),
                Chara (false, false, false, false, false, true, false, false),
                Chara (true, true, false, false, false, false, true, false),
                Chara (true, false, false, false, false, true, true, false),
                Chara (false, true, true, true, false, true, true, false),
                Chara (false, true, true, true, false, true, true, false),
                Chara (true, true, true, true, false, true, true, false),
                Chara (false, false, true, false, true, true, true, false),
                Chara (false, false, false, false, false, true, false, false),
                Chara (false, false, false, false, true, true, true, false),
                Chara (true, false, false, false, false, true, true, false),
                Chara (false, true, false, false, true, true, true, false),
                Chara (true, true, false, false, true, true, true, false),
                Chara (true, false, true, false, false, true, true, false),
                Chara (false, false, false, false, false, true, false, false),
                Chara (false, false, true, false, false, true, true, false),
                Chara (true, false, false, false, false, true, true, false),
                Chara (false, false, true, false, true, true, true, false),
                Chara (true, false, false, false, false, true, true, false),
                Chara (false, true, true, true, false, true, false, false)]
          | SOME valuea =>
            (case encodea valuea
              of Inl valueb =>
                implode
                  ([Chara (true, true, true, true, false, false, true, false),
                     Chara (true, true, false, true, false, false, true, false),
                     Chara (false, true, false, true, true, true, false, false),
                     Chara (false, false, false, false, false, true, false,
                             false),
                     Chara (false, false, false, false, true, true, false,
                             false),
                     Chara (false, false, false, true, true, true, true,
                             false)] @
                    writeHex valueb)
              | Inr msg =>
                implode
                  ([Chara (true, false, true, false, false, false, true, false),
                     Chara (false, true, false, false, true, false, true,
                             false),
                     Chara (false, true, false, false, true, false, true,
                             false),
                     Chara (false, true, false, true, true, true, false, false),
                     Chara (false, false, false, false, false, true, false,
                             false)] @
                    msg)))))
    x;

end; (*struct ABICoder*)

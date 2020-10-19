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

datatype int = Int_of_integer of IntInf.int;

datatype num = One | Bit0 of num | Bit1 of num;

val one_inta : int = Int_of_integer (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = one_inta} : int one;

fun integer_of_int (Int_of_integer k) = k;

fun times_inta k l =
  Int_of_integer (IntInf.* (integer_of_int k, integer_of_int l));

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_int = {times = times_inta} : int times;

val power_int = {one_power = one_int, times_power = times_int} : int power;

datatype rat = Frct of (int * int);

val one_rata : rat = Frct (one_inta, one_inta);

val one_rat = {one = one_rata} : rat one;

fun quotient_of (Frct x) = x;

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

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_int k l =
  Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

fun uminus_int k = Int_of_integer (IntInf.~ (integer_of_int k));

fun equal_int k l = (((integer_of_int k) : IntInf.int) = (integer_of_int l));

val zero_int : int = Int_of_integer (0 : IntInf.int);

fun less_int k l = IntInf.< (integer_of_int k, integer_of_int l);

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

fun gcd_integer k l =
  IntInf.abs
    (if ((l : IntInf.int) = (0 : IntInf.int)) then k
      else gcd_integer l (modulo_integer (IntInf.abs k) (IntInf.abs l)));

fun gcd_int (Int_of_integer x) (Int_of_integer y) =
  Int_of_integer (gcd_integer x y);

fun normalize p =
  (if less_int zero_int (snd p)
    then let
           val a = gcd_int (fst p) (snd p);
         in
           (divide_int (fst p) a, divide_int (snd p) a)
         end
    else (if equal_int (snd p) zero_int then (zero_int, one_inta)
           else let
                  val a = uminus_int (gcd_int (fst p) (snd p));
                in
                  (divide_int (fst p) a, divide_int (snd p) a)
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

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

datatype nat = Nat of IntInf.int;

datatype 'a itself = Type;

type 'a len0 = {len_of : 'a itself -> nat};
val len_of = #len_of : 'a len0 -> 'a itself -> nat;

datatype 'a word = Word of int;

fun uint A_ (Word x) = x;

fun equal_worda A_ k l = equal_int (uint A_ k) (uint A_ l);

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

fun integer_of_nat (Nat x) = x;

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

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

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

type 'a finite = {};

datatype 'a bit0 = Abs_bit0 of int;

fun len_of_bit0 A_ uu =
  times_nat (nat_of_integer (2 : IntInf.int)) (len_of A_ Type);

type 'a len = {len0_len : 'a len0};
val len0_len = #len0_len : 'a len -> 'a len0;

fun len0_bit0 A_ = {len_of = len_of_bit0 A_} : 'a bit0 len0;

fun len_bit0 A_ = {len0_len = len0_bit0 (len0_len A_)} : 'a bit0 len;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

datatype 'a bit1 = Abs_bit1 of int;

fun len_of_bit1 A_ uu =
  plus_nat (times_nat (nat_of_integer (2 : IntInf.int)) (len_of A_ Type))
    one_nat;

fun len0_bit1 A_ = {len_of = len_of_bit1 A_} : 'a bit1 len0;

datatype num1 = One_num1;

fun len_of_num1 uu = one_nat;

val len0_num1 = {len_of = len_of_num1} : num1 len0;

val len_num1 = {len0_len = len0_num1} : num1 len;

val one_integera : IntInf.int = (1 : IntInf.int);

val one_integer = {one = one_integera} : IntInf.int one;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

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

fun nat k = Nat (max ord_integer (0 : IntInf.int) (integer_of_int k));

fun suc n = plus_nat n one_nat;

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
  | zip xs [] = []
  | zip [] ys = [];

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

val zero_nat : nat = Nat (0 : IntInf.int);

fun drop n [] = []
  | drop n (x :: xs) =
    (if equal_nat n zero_nat then x :: xs else drop (minus_nat n one_nat) xs);

fun null [] = true
  | null (x :: xs) = false;

fun take n [] = []
  | take n (x :: xs) =
    (if equal_nat n zero_nat then [] else x :: take (minus_nat n one_nat) xs);

fun bin_rest w = divide_int w (Int_of_integer (2 : IntInf.int));

fun modulo_int k l =
  Int_of_integer (modulo_integer (integer_of_int k) (integer_of_int l));

fun bin_last w =
  equal_int (modulo_int w (Int_of_integer (2 : IntInf.int))) one_inta;

fun plus_int k l =
  Int_of_integer (IntInf.+ (integer_of_int k, integer_of_int l));

fun bit k b = plus_int (plus_int (if b then one_inta else zero_int) k) k;

fun sbintrunc n bin =
  (if equal_nat n zero_nat
    then (if bin_last bin then uminus_int one_inta else zero_int)
    else bit (sbintrunc (minus_nat n one_nat) (bin_rest bin)) (bin_last bin));

fun sint A_ w =
  sbintrunc (minus_nat (len_of (len0_len A_) Type) one_nat)
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

fun funpow n f =
  (if equal_nat n zero_nat then id else f o funpow (minus_nat n one_nat) f);

fun of_int a = Frct (a, one_inta);

fun power A_ a n =
  (if equal_nat n zero_nat then one (one_power A_)
    else times (times_power A_) a (power A_ a (minus_nat n one_nat)));

fun word_of_int A_ k =
  Word (modulo_int k
         (power power_int (Int_of_integer (2 : IntInf.int)) (len_of A_ Type)));

fun ucast A_ B_ w = word_of_int B_ (uint A_ w);

fun fun_upd A_ f a b = (fn x => (if eq A_ x a then b else f x));

fun concat xss = foldr (fn a => fn b => a @ b) xss [];

fun bind NONE f = NONE
  | bind (SOME x) f = f x;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun map_prod f g (a, b) = (f a, g b);

fun divmod_nat m n =
  let
    val k = integer_of_nat m;
    val l = integer_of_nat n;
  in
    map_prod nat_of_integer nat_of_integer
      (if ((k : IntInf.int) = (0 : IntInf.int))
        then ((0 : IntInf.int), (0 : IntInf.int))
        else (if ((l : IntInf.int) = (0 : IntInf.int))
               then ((0 : IntInf.int), k)
               else IntInf.divMod (IntInf.abs k, IntInf.abs l)))
  end;

fun decwrite1 c =
  (if equal_nat c zero_nat
    then Chara (false, false, false, false, true, true, false, false)
    else (if equal_nat c one_nat
           then Chara (true, false, false, false, true, true, false, false)
           else (if equal_nat c (nat_of_integer (2 : IntInf.int))
                  then Chara (false, true, false, false, true, true, false,
                               false)
                  else (if equal_nat c (nat_of_integer (3 : IntInf.int))
                         then Chara (true, true, false, false, true, true,
                                      false, false)
                         else (if equal_nat c (nat_of_integer (4 : IntInf.int))
                                then Chara (false, false, true, false, true,
     true, false, false)
                                else (if equal_nat c
   (nat_of_integer (5 : IntInf.int))
                                       then Chara
      (true, false, true, false, true, true, false, false)
                                       else (if equal_nat c
          (nat_of_integer (6 : IntInf.int))
      then Chara (false, true, true, false, true, true, false, false)
      else (if equal_nat c (nat_of_integer (7 : IntInf.int))
             then Chara (true, true, true, false, true, true, false, false)
             else (if equal_nat c (nat_of_integer (8 : IntInf.int))
                    then Chara (false, false, false, true, true, true, false,
                                 false)
                    else (if equal_nat c (nat_of_integer (9 : IntInf.int))
                           then Chara (true, false, false, true, true, true,
false, false)
                           else (raise Fail "undefined")))))))))));

fun decwritea n =
  (if less_nat n (nat_of_integer (10 : IntInf.int)) then [decwrite1 n]
    else let
           val (d, m) = divmod_nat n (nat_of_integer (10 : IntInf.int));
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

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun minus_int k l =
  Int_of_integer (IntInf.- (integer_of_int k, integer_of_int l));

fun of_bool A_ true = one (one_zero_neq_one A_)
  | of_bool A_ false = zero (zero_zero_neq_one A_);

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

fun nat_of_char c = Nat (integer_of_char c);

fun int_of_char x = (Int_of_integer o integer_of_char) x;

fun is_digit x =
  (fn c =>
    less_eq_nat
      (nat_of_char
        (Chara (false, false, false, false, true, true, false, false)))
      (nat_of_char c) andalso
      less_eq_nat (nat_of_char c)
        (nat_of_char
          (Chara (true, false, false, true, true, true, false, false))))
    x;

fun parseHexDigit x =
  (if is_digit x
    then SOME (minus_int (int_of_char x)
                (int_of_char
                  (Chara
                    (false, false, false, false, true, true, false, false))))
    else (if less_eq_nat
               (nat_of_char
                 (Chara (true, false, false, false, false, false, true, false)))
               (nat_of_char x) andalso
               less_eq_nat (nat_of_char x)
                 (nat_of_char
                   (Chara
                     (false, true, true, false, false, false, true, false)))
           then SOME (plus_int
                       (minus_int (int_of_char x)
                         (int_of_char
                           (Chara
                             (true, false, false, false, false, false, true,
                               false))))
                       (Int_of_integer (10 : IntInf.int)))
           else (if less_eq_nat
                      (nat_of_char
                        (Chara
                          (true, false, false, false, false, true, true,
                            false)))
                      (nat_of_char x) andalso
                      less_eq_nat (nat_of_char x)
                        (nat_of_char
                          (Chara
                            (false, true, true, false, false, true, true,
                              false)))
                  then SOME (plus_int
                              (minus_int (int_of_char x)
                                (int_of_char
                                  (Chara
                                    (true, false, false, false, false, true,
                                      true, false))))
                              (Int_of_integer (10 : IntInf.int)))
                  else NONE)));

fun parseWord x =
  (fn xa => fn y =>
    (case (parseHexDigit xa, parseHexDigit y) of (NONE, _) => NONE
      | (SOME _, NONE) => NONE
      | (SOME xb, SOME ya) =>
        SOME (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
               (plus_int (times_inta xb (Int_of_integer (16 : IntInf.int)))
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

fun bin_split n w =
  (if equal_nat n zero_nat then (w, zero_int)
    else let
           val (w1, w2) = bin_split (minus_nat n one_nat) (bin_rest w);
         in
           (w1, bit w2 (bin_last w))
         end);

fun bin_rsplit_aux n m c bs =
  (if equal_nat m zero_nat orelse equal_nat n zero_nat then bs
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

fun char_of_int x = (char_of_integer o integer_of_int) x;

fun writeInt n =
  (if less_int n zero_int
    then Chara (true, false, true, true, false, true, false, false) ::
           writeInt (uminus_int n)
    else (if less_int n (Int_of_integer (10 : IntInf.int))
           then [char_of_int
                   (plus_int
                     (int_of_char
                       (Chara
                         (false, false, false, false, true, true, false,
                           false)))
                     n)]
           else writeInt (divide_int n (Int_of_integer (10 : IntInf.int))) @
                  writeInt (modulo_int n (Int_of_integer (10 : IntInf.int)))));

fun shiftr_word A_ w n = funpow n (shiftr1 A_) w;

fun bitAND_int x y =
  (if equal_int x zero_int then zero_int
    else (if equal_int x (uminus_int one_inta) then y
           else bit (bitAND_int (bin_rest x) (bin_rest y))
                  (bin_last x andalso bin_last y)));

fun bitAND_word A_ a b = word_of_int A_ (bitAND_int (uint A_ a) (uint A_ b));

fun less_word A_ a b = less_int (uint A_ a) (uint A_ b);

fun writeHexNibble x =
  (if less_word (len0_bit0 (len0_bit0 len0_num1)) x
        (word_of_int (len0_bit0 (len0_bit0 len0_num1))
          (Int_of_integer (10 : IntInf.int)))
    then char_of_int
           (plus_int
             (int_of_char
               (Chara (false, false, false, false, true, true, false, false)))
             (uint (len0_bit0 (len0_bit0 len0_num1)) x))
    else char_of_int
           (minus_int
             (plus_int
               (int_of_char
                 (Chara (true, false, false, false, false, false, true, false)))
               (uint (len0_bit0 (len0_bit0 len0_num1)) x))
             (Int_of_integer (10 : IntInf.int))));

fun writeHexDigit x =
  [writeHexNibble
     (ucast (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
       (len0_bit0 (len0_bit0 len0_num1))
       (shiftr_word (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) x
         (nat_of_integer (4 : IntInf.int)))),
    writeHexNibble
      (ucast (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (len0_bit0 (len0_bit0 len0_num1))
        (bitAND_word (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) x
          (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
            (Int_of_integer (15 : IntInf.int)))))];

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
                 (int_of_char x))
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

fun less_eq_int k l = IntInf.<= (integer_of_int k, integer_of_int l);

fun parseNatRev (x :: xs) =
  let
    val v = int_of_char x;
  in
    (if less_eq_int
          (int_of_char
            (Chara (false, false, false, false, true, true, false, false)))
          v andalso
          less_eq_int v
            (int_of_char
              (Chara (true, false, false, true, true, true, false, false)))
      then (case parseNatRev xs of NONE => NONE
             | SOME vs =>
               SOME (plus_int
                      (minus_int v
                        (int_of_char
                          (Chara
                            (false, false, false, false, true, true, false,
                              false))))
                      (times_inta (Int_of_integer (10 : IntInf.int)) vs)))
      else NONE)
  end
  | parseNatRev [] = SOME zero_int;

fun parseNat x = (fn xa => map_option nat (parseNatRev (rev xa))) x;

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

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun abi_type_valid (Tuint n) =
  less_nat zero_nat n andalso
    (less_eq_nat n (nat_of_integer (256 : IntInf.int)) andalso
      equal_nat (modulo_nat n (nat_of_integer (8 : IntInf.int))) zero_nat)
  | abi_type_valid (Tsint n) =
    less_nat zero_nat n andalso
      (less_eq_nat n (nat_of_integer (256 : IntInf.int)) andalso
        equal_nat (modulo_nat n (nat_of_integer (8 : IntInf.int))) zero_nat)
  | abi_type_valid (Tfixed (m, n)) =
    less_eq_nat (nat_of_integer (8 : IntInf.int)) m andalso
      (less_eq_nat m (nat_of_integer (256 : IntInf.int)) andalso
        (equal_nat (modulo_nat m (nat_of_integer (8 : IntInf.int)))
           zero_nat andalso
          (less_nat zero_nat n andalso
            less_eq_nat n (nat_of_integer (80 : IntInf.int)))))
  | abi_type_valid (Tufixed (m, n)) =
    less_eq_nat (nat_of_integer (8 : IntInf.int)) m andalso
      (less_eq_nat m (nat_of_integer (256 : IntInf.int)) andalso
        (equal_nat (modulo_nat m (nat_of_integer (8 : IntInf.int)))
           zero_nat andalso
          (less_nat zero_nat n andalso
            less_eq_nat n (nat_of_integer (80 : IntInf.int)))))
  | abi_type_valid (Tfbytes m) =
    less_nat zero_nat m andalso less_eq_nat m (nat_of_integer (32 : IntInf.int))
  | abi_type_valid (Tfarray (t, uu)) = abi_type_valid t
  | abi_type_valid (Ttuple ts) = list_all abi_type_valid ts
  | abi_type_valid (Tarray t) = abi_type_valid t
  | abi_type_valid Taddr = true
  | abi_type_valid Tbool = true
  | abi_type_valid Tfunction = true
  | abi_type_valid Tbytes = true
  | abi_type_valid Tstring = true;

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun size_list x = gen_length zero_nat x;

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

fun int_of_nat n = Int_of_integer (integer_of_nat n);

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

fun abi_static_size (Tuint n) = Int_of_integer (32 : IntInf.int)
  | abi_static_size (Tsint n) = Int_of_integer (32 : IntInf.int)
  | abi_static_size Taddr = Int_of_integer (32 : IntInf.int)
  | abi_static_size Tbool = Int_of_integer (32 : IntInf.int)
  | abi_static_size (Tfixed (uu, uv)) = Int_of_integer (32 : IntInf.int)
  | abi_static_size (Tufixed (uw, ux)) = Int_of_integer (32 : IntInf.int)
  | abi_static_size (Tfbytes uy) = Int_of_integer (32 : IntInf.int)
  | abi_static_size Tfunction = Int_of_integer (32 : IntInf.int)
  | abi_static_size (Tfarray (t, n)) =
    times_inta (int_of_nat n) (abi_static_size t)
  | abi_static_size (Ttuple ts) =
    foldl (fn a => fn x => plus_int a (abi_static_size x)) zero_int ts
  | abi_static_size Tbytes = zero_int
  | abi_static_size Tstring = zero_int
  | abi_static_size (Tarray v) = zero_int;

fun bin_cat w n v =
  (if equal_nat n zero_nat then w
    else bit (bin_cat w (minus_nat n one_nat) (bin_rest v)) (bin_last v));

fun bin_rcat n = foldl (fn u => bin_cat u n) zero_int;

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
      (take (nat_of_integer (32 : IntInf.int)) l));

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

fun max_uint n =
  minus_int (power power_int (Int_of_integer (2 : IntInf.int)) n) one_inta;

fun uint_value_valid n i =
  less_eq_int zero_int i andalso less_eq_int i (max_uint n);

fun function_value_valid i1 i2 =
  uint_value_valid (nat_of_integer (160 : IntInf.int)) i1 andalso
    uint_value_valid (nat_of_integer (32 : IntInf.int)) i2;

fun skip_padding n =
  let
    val (_, na) = divmod_nat n (nat_of_integer (32 : IntInf.int));
  in
    (if equal_nat na zero_nat then n
      else minus_nat (plus_nat n (nat_of_integer (32 : IntInf.int)))
             (suc (minus_nat na one_nat)))
  end;

fun replicate n x =
  (if equal_nat n zero_nat then [] else x :: replicate (minus_nat n one_nat) x);

fun check_padding n l =
  let
    val p = skip_padding n;
  in
    less_eq_nat p (size_list l) andalso
      equal_lista (equal_word (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))))
        (drop n (take p l))
        (replicate (minus_nat p n)
          (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) zero_int))
  end;

fun decode_function_sel bs =
  (if check_padding (nat_of_integer (24 : IntInf.int)) bs
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
                   (take (nat_of_integer (20 : IntInf.int)) bs)),
                uint (len0_bit0
                       (len0_bit0
                         (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
                  (word_rcat (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                    (len0_bit0
                      (len0_bit0 (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))))
                    (take (nat_of_integer (4 : IntInf.int))
                      (drop (nat_of_integer (20 : IntInf.int)) bs))))
    else NONE);

fun int_of_fixed n r =
  let
    val (num, den) =
      quotient_of
        (times_rata r
          (power power_rat (of_int (Int_of_integer (10 : IntInf.int))) n));
  in
    (if equal_int den one_inta then SOME num else NONE)
  end;

fun ufixed_value_valid m n r =
  (case int_of_fixed n r of NONE => false
    | SOME i => less_eq_int zero_int i andalso less_eq_int i (max_uint m));

fun fbytes_value_valid n l = equal_nat (size_list l) n;

fun min_sint n =
  times_inta (uminus_int one_inta)
    (power power_int (Int_of_integer (2 : IntInf.int)) (minus_nat n one_nat));

fun max_sint n =
  minus_int
    (power power_int (Int_of_integer (2 : IntInf.int)) (minus_nat n one_nat))
    one_inta;

fun fixed_value_valid m n r =
  (case int_of_fixed n r of NONE => false
    | SOME i => less_eq_int (min_sint m) i andalso less_eq_int i (max_sint m));

fun sint_value_valid n i =
  less_eq_int (min_sint n) i andalso less_eq_int i (max_sint n);

fun addr_value_valid i = uint_value_valid (nat_of_integer (160 : IntInf.int)) i;

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
      (take (nat_of_integer (32 : IntInf.int)) l));

fun decode_ufixed n l =
  let
    val i = decode_uint l;
  in
    divide_rat (of_int i)
      (power power_rat (of_int (Int_of_integer (10 : IntInf.int))) n)
  end;

fun decode_fbytes n l = (if check_padding n l then SOME (take n l) else NONE);

fun decode_fixed n l =
  let
    val i = decode_sint l;
  in
    divide_rat (of_int i)
      (power power_rat (of_int (Int_of_integer (10 : IntInf.int))) n)
  end;

fun decode_bool l =
  let
    val i = decode_uint l;
  in
    (if equal_int i zero_int then SOME false
      else (if equal_int i one_inta then SOME true else NONE))
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
        (case decode_static_tup ts (plus_int ix (abi_static_size t), l)
          of Inl vs => Inl (v :: vs) | Inr a => Inr a)
      | Inr a => Inr a);

fun decodeb t (ix, l) =
  (if less_int ix zero_int
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
    else (if less_int (int_of_nat (size_list l)) ix
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
                    then (if less_int (int_of_nat (size_list l))
                               (plus_int (abi_static_size t) ix)
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
                               val ts = replicate (nat (int_of_nat n)) ta;
                             in
                               (case decode_dyn_tuple_heads ts zero_int (ix, l)
                                 of Inl (vos,
  (idxs, (byteoffset, bytes_parsed)))
                                   => (case
decode_dyn_tuple_tails idxs ts vos byteoffset (ix, l)
of Inl (vs, bytes_parseda) =>
  Inl (Vfarray (ta, n, vs), plus_int bytes_parsed bytes_parseda)
| Inr a => Inr a)
                                 | Inr a => Inr a)
                             end
                           | Ttuple ts =>
                             (case decode_dyn_tuple_heads ts zero_int (ix, l)
                               of Inl (vos, (idxs, (byteoffset, bytes_parsed)))
                                 => (case decode_dyn_tuple_tails idxs ts vos
    byteoffset (ix, l)
                                      of Inl (vs, bytes_parseda) =>
Inl (Vtuple (ts, vs), plus_int bytes_parsed bytes_parseda)
                                      | Inr a => Inr a)
                               | Inr a => Inr a)
                           | Tbytes =>
                             (if less_int (int_of_nat (size_list l))
                                   (plus_int (Int_of_integer (32 : IntInf.int))
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
decode_uint (take (nat_of_integer (32 : IntInf.int)) la);
                                    in
                                      (if less_int (int_of_nat (size_list l))
    (plus_int (plus_int sz (Int_of_integer (32 : IntInf.int))) ix)
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
else (if check_padding (nat sz) (drop (nat_of_integer (32 : IntInf.int)) la)
       then Inl (Vbytes
                   (take (nat sz) (drop (nat_of_integer (32 : IntInf.int)) la)),
                  plus_int (int_of_nat (skip_padding (nat sz)))
                    (Int_of_integer (32 : IntInf.int)))
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
                             (if less_int (int_of_nat (size_list l))
                                   (plus_int (Int_of_integer (32 : IntInf.int))
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
decode_uint (take (nat_of_integer (32 : IntInf.int)) la);
                                    in
                                      (if less_int (int_of_nat (size_list l))
    (plus_int (plus_int sz (Int_of_integer (32 : IntInf.int))) ix)
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
else (if check_padding (nat sz) (drop (nat_of_integer (32 : IntInf.int)) la)
       then Inl (Vstring
                   (bytes_to_string
                     (take (nat sz)
                       (drop (nat_of_integer (32 : IntInf.int)) la))),
                  plus_int (int_of_nat (skip_padding (nat sz)))
                    (Int_of_integer (32 : IntInf.int)))
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
                             (if less_int (int_of_nat (size_list l))
                                   (plus_int (Int_of_integer (32 : IntInf.int))
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
decode_uint (take (nat_of_integer (32 : IntInf.int)) la);
                                      val ts = replicate (nat n) ta;
                                    in
                                      (case
decode_dyn_tuple_heads ts zero_int
  (plus_int ix (Int_of_integer (32 : IntInf.int)), l)
of Inl (vos, (idxs, (byteoffset, bytes_parsed))) =>
  (case decode_dyn_tuple_tails idxs ts vos byteoffset
          (plus_int ix (Int_of_integer (32 : IntInf.int)), l)
    of Inl (vs, bytes_parseda) =>
      Inl (Varray (ta, vs),
            plus_int (plus_int bytes_parsed bytes_parseda)
              (Int_of_integer (32 : IntInf.int)))
    | Inr a => Inr a)
| Inr a => Inr a)
                                    end)))
                end))
and decode_dyn_tuple_heads [] n (ix, l) = Inl ([], ([], (n, zero_int)))
  | decode_dyn_tuple_heads (th :: tt) n (ix, l) =
    let
      val la = drop (nat (plus_int ix n)) l;
    in
      (if abi_type_isstatic th
        then (case decodeb th (plus_int ix n, l)
               of Inl (v, bytes_parsed) =>
                 (case decode_dyn_tuple_heads tt
                         (plus_int n (int_of_nat (nat (abi_static_size th))))
                         (ix, l)
                   of Inl (vos, (idxs, (na, bytes_parseda))) =>
                     Inl (SOME v :: vos,
                           (NONE :: idxs,
                             (na, plus_int bytes_parsed bytes_parseda)))
                   | Inr a => Inr a)
               | Inr a => Inr a)
        else (if less_nat (size_list la) (nat_of_integer (32 : IntInf.int))
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
                          (take (nat_of_integer (32 : IntInf.int)) la);
                    in
                      (case decode_dyn_tuple_heads tt
                              (plus_int n (Int_of_integer (32 : IntInf.int)))
                              (ix, l)
                        of Inl (vos, (idxs, (na, bytes_parsed))) =>
                          Inl (NONE :: vos,
                                (SOME (plus_int ix sz) :: idxs,
                                  (na, plus_int bytes_parsed
 (Int_of_integer (32 : IntInf.int)))))
                        | Inr a => Inr a)
                    end))
    end
and decode_dyn_tuple_tails [] [] [] uu (ix, l) = Inl ([], zero_int)
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
            val offseta = plus_int offset bytes_parsed;
          in
            (case decode_dyn_tuple_tails t tt vt offseta (ix, l)
              of Inl (vs, bytes_parseda) =>
                Inl (v :: vs, plus_int bytes_parsed bytes_parseda)
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
    then (case decodeb t (zero_int, l) of Inl (v, _) => Inl v | Inr a => Inr a)
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
        (if equal_nat (size_list w) (nat_of_integer (4 : IntInf.int))
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
        (if equal_nat (size_list w) (nat_of_integer (20 : IntInf.int))
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

fun parseUint x = (fn str => map_option int_of_nat (parseNat str)) x;

fun parseSint
  (Chara (true, false, true, true, false, true, false, false) :: tail) =
  map_option (fn n => uminus_int (int_of_nat n)) (parseNat tail)
  | parseSint [] = map_option int_of_nat (parseNat [])
  | parseSint (Chara (false, vc, vd, ve, vf, vg, vh, vi) :: va) =
    map_option int_of_nat
      (parseNat (Chara (false, vc, vd, ve, vf, vg, vh, vi) :: va))
  | parseSint (Chara (vb, true, vd, ve, vf, vg, vh, vi) :: va) =
    map_option int_of_nat
      (parseNat (Chara (vb, true, vd, ve, vf, vg, vh, vi) :: va))
  | parseSint (Chara (vb, vc, false, ve, vf, vg, vh, vi) :: va) =
    map_option int_of_nat
      (parseNat (Chara (vb, vc, false, ve, vf, vg, vh, vi) :: va))
  | parseSint (Chara (vb, vc, vd, false, vf, vg, vh, vi) :: va) =
    map_option int_of_nat
      (parseNat (Chara (vb, vc, vd, false, vf, vg, vh, vi) :: va))
  | parseSint (Chara (vb, vc, vd, ve, true, vg, vh, vi) :: va) =
    map_option int_of_nat
      (parseNat (Chara (vb, vc, vd, ve, true, vg, vh, vi) :: va))
  | parseSint (Chara (vb, vc, vd, ve, vf, false, vh, vi) :: va) =
    map_option int_of_nat
      (parseNat (Chara (vb, vc, vd, ve, vf, false, vh, vi) :: va))
  | parseSint (Chara (vb, vc, vd, ve, vf, vg, true, vi) :: va) =
    map_option int_of_nat
      (parseNat (Chara (vb, vc, vd, ve, vf, vg, true, vi) :: va))
  | parseSint (Chara (vb, vc, vd, ve, vf, vg, vh, true) :: va) =
    map_option int_of_nat
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
               char_of_int
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
  uint_value_valid (nat_of_integer (256 : IntInf.int))
    (int_of_nat (size_list l)) andalso
    list_all (fn v => equal_abi_typea (abi_get_type v) t) l;

fun string_value_valid s =
  uint_value_valid (nat_of_integer (256 : IntInf.int))
    (int_of_nat (size_list s));

fun bytes_value_valid bs =
  uint_value_valid (nat_of_integer (256 : IntInf.int))
    (int_of_nat (size_list bs));

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

fun string_to_bytes s =
  map (fn c =>
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (integer_of_char c)))
    s;

fun pad_bytes l =
  let
    val (_, n) = divmod_nat (size_list l) (nat_of_integer (32 : IntInf.int));
  in
    (if equal_nat n zero_nat then l
      else l @ replicate
                 (minus_nat (nat_of_integer (32 : IntInf.int))
                   (suc (minus_nat n one_nat)))
                 (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                   zero_int))
  end;

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
             (power power_rat (of_int (Int_of_integer (10 : IntInf.int))) n))));

fun encode_bool true = encode_int one_inta
  | encode_bool false = encode_int zero_int;

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

fun heads_length [] = zero_int
  | heads_length (h :: t) =
    let
      val tyh = abi_get_type h;
    in
      (if abi_type_isstatic tyh
        then plus_int (abi_static_size tyh) (heads_length t)
        else plus_int (Int_of_integer (32 : IntInf.int)) (heads_length t))
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
             (case encode_tuple_tails vs zero_int (heads_length vs)
               of Inl bvs =>
                 (case encode_tuple_heads vs bvs
                   of Inl (heads, tails) => Inl (heads @ tails)
                   | Inr a => Inr a)
               | Inr a => Inr a)
           | Vtuple (_, vs) =>
             (case encode_tuple_tails vs zero_int (heads_length vs)
               of Inl bvs =>
                 (case encode_tuple_heads vs bvs
                   of Inl (heads, tails) => Inl (heads @ tails)
                   | Inr a => Inr a)
               | Inr a => Inr a)
           | Vbytes l =>
             Inl (encode_int (int_of_nat (size_list l)) @ pad_bytes l)
           | Vstring s =>
             let
               val bs = string_to_bytes s;
             in
               Inl (encode_int (int_of_nat (size_list bs)) @ pad_bytes bs)
             end
           | Varray (_, vs) =>
             (case encode_tuple_tails vs zero_int (heads_length vs)
               of Inl bvs =>
                 (case encode_tuple_heads vs bvs
                   of Inl (heads, tails) =>
                     Inl (encode_int (int_of_nat (size_list vs)) @
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
             of Inl ts => Inl ((plus_int len_total headlen, []) :: ts)
             | Inr a => Inr a)
      else (case encodeb v
             of Inl enc =>
               let
                 val len_totala =
                   plus_int len_total (int_of_nat (size_list enc));
               in
                 (case encode_tuple_tails rest headlen len_totala
                   of Inl ts =>
                     (if sint_value_valid (nat_of_integer (256 : IntInf.int))
                           (plus_int len_total headlen)
                       then Inl ((plus_int len_total headlen, enc) :: ts)
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

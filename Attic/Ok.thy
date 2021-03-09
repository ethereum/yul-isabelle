theory Ok imports Main

begin

(* A quick-and-dirty approach for getting error messages out of functions
   using the sum type *)
type_synonym 'a orerror = "'a + char list"

abbreviation Ok :: "'a \<Rightarrow> 'a orerror" where
"Ok \<equiv> Inl"

abbreviation Err :: "char list \<Rightarrow> 'a orerror" where
"Err \<equiv> Inr"

fun those_err :: "'a orerror list \<Rightarrow> 'a list orerror" where
"those_err [] = Ok []"
| "those_err ((Ok h)#t) = 
    (case those_err t of
      Err s \<Rightarrow> Err s
      | Ok t' \<Rightarrow> Ok (h#t'))"
| "those_err ((Err s)#_) = Err s"

fun map_err :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a orerror) \<Rightarrow> ('b orerror)" where
"map_err f (Ok a) = (Ok (f a))"
| "map_err f (Err s) = Err s"

fun bind_err :: "('a \<Rightarrow> 'b orerror) \<Rightarrow> ('a orerror) \<Rightarrow> ('b orerror)" where
"bind_err f (Ok a) = f a"
| "bind_err f (Err s) = Err s"

end
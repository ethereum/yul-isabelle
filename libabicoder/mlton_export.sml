val toList = (fn v => Vector.foldr (op::) [] v);
val e = _export "abicoder_decode": (char vector*char vector -> char vector) -> unit;
val _ = e (fn (x,y) => Vector.fromList (explode (ABICoder.decode (implode (toList x)) (implode (toList y)))));
val e = _export "abicoder_alloc": (int -> char vector) -> unit;
val _ = e(fn len => Vector.tabulate (len,fn _ => chr 0));
val e = _export "abicoder_size": (char vector -> int) -> unit;
val _ = e(fn x => Vector.length x);
theory Indexing imports "../Yul/YulSyntax"
begin

(* index into a syntax tree, yielding either an expression or statement. *)
datatype YulNodeD =
  Node nat
  | ForCond
  | ForPre
  | ForBody
  | ForPost
  | SwitchCase nat nat

type_synonym YulIndex = 
  "YulNodeD list"

fun yul_idx_get ::
  "(('v, 't) YulStatement + ('v, 't) YulExpression) \<Rightarrow>
   YulIndex \<Rightarrow>
   (('v, 't) YulStatement + ('v, 't) YulExpression) option" where
"yul_idx_get
  x [] = Some x"

(* Raw function calls *)
| "yul_idx_get 
  (Inl (YulFunctionCallStatement (YulFunctionCall _ args))) 
  ((Node n)#t) =
  (if length args < n then None
   else yul_idx_get (Inr (args ! n)) t)"
| "yul_idx_get
  (Inr (YulFunctionCallExpression (YulFunctionCall _ args)))
  ((Node n)#t) =
  (if length args < n then None
   else yul_idx_get (Inr (args ! n)) t)"

(* Assignments and declarations, if RHS is a function call *)
| "yul_idx_get
   (Inl (YulAssignmentStatement (YulAssignment _ (YulFunctionCallExpression (YulFunctionCall _ args)))))
   ((Node n)#t) =
   (if length args < n then None
    else yul_idx_get (Inr (args ! n)) t)"
(* Assignments and declarations, if RHS is a function call *)
| "yul_idx_get
   (Inl (YulVariableDeclarationStatement
        (YulVariableDeclaration _
          (Some (YulFunctionCallExpression (YulFunctionCall _ args))))))
   ((Node n)#t) =
   (if length args < n then None
    else yul_idx_get (Inr (args ! n)) t)"

| "yul_idx_get
  (Inl (YulBlock l))
  ((Node n)#t) =
    (if length l < n then None
     else yul_idx_get (Inl (l ! n)) t)"

| "yul_idx_get
  (Inl (YulIf _ l)) ((SiIf, n)#t)=
    (if length l < n then None
     else yul_idx_get (Inl (l ! n)) t)"

| "yul_idx_get
  (Inl (YulFunctionDefinitionStatement (YulFunctionDefinition _ _ _ l)))
  ((SiFunctionBody, n)#t) =
    (if length l < n then None
     else yul_idx_get (Inl (l!n)) t)"

| "yul_idx_get 
    (Inl (YulForLoop l _ _ _)) 
    ((SiForPre, n)#t) =
    (if length l < n then None
     else yul_idx_get (Inl (l!n)) t)"
| "yul_idx_get (YulForLoop _ _ l _)
    ((SiForBody, n)#t) =
    (if length l < n then None
     else yul_idx_get (l!n) t)"
| "yul_idx_get (YulForLoop _ _ _ l) (n#t) =
    (if length l < n then None
     else yul_idx_get (l!n) t)"
| "yul_idx_get _ _ = None"

fun yul_statement_update ::
  "(('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement) \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   YulIndex \<Rightarrow>
   ('v, 't) YulStatement option" where
"yul_statement_update
  f x [] = Some (f x)"
| "yul_statement_update f
  (YulBlock l) ((n)#t) =
    (if length l < n then None
     else (case yul_statement_update f (l ! n) t of
      None \<Rightarrow> None
      | Some ln' \<Rightarrow> Some (YulBlock (take n l @ ln' # drop (n+1) l))))"
| "yul_statement_update f
  (YulIf c l) ((n)#t)=
    (if length l < n then None
     else (case yul_statement_update f (l ! n) t of
      None \<Rightarrow> None
      | Some ln' \<Rightarrow> Some (YulIf c (take n l @ ln' # drop (n +1) l))))"
| "yul_statement_update f
  (YulFunctionDefinitionStatement
    (YulFunctionDefinition x1 x2 x3 l)) ((n)#t) =
    (if length l < n then None
     else (case yul_statement_update f (l!n) t of
      None \<Rightarrow> None
      | Some ln' \<Rightarrow> Some (YulFunctionDefinitionStatement (YulFunctionDefinition
          x1 x2 x3
          (take n l @ ln' # drop (n+1) l)))))"
| "yul_statement_update f (YulForLoop l x2 x3 x4) ((n)#t) =
    (if length l < n then None
     else (case yul_statement_update f (l!n) t of
      None \<Rightarrow> None
      | Some ln' \<Rightarrow> Some (YulForLoop (take n l @ ln' # drop (n+1) l) x2 x3 x4)))"
| "yul_statement_update f (YulForLoop x1 x2 l x4) ((SiForBody, n)#t) =
    (if length l < n then None
     else (case yul_statement_update f (l!n) t of
      None \<Rightarrow> None
      | Some ln' \<Rightarrow> Some (YulForLoop x1 x2 (take n l @ ln' # drop (n+1) l) x4)))"
| "yul_statement_update f (YulForLoop x1 x2 x3 l) ((SiForPost, n)#t) =
    (if length l < n then None
     else (case yul_statement_update f (l!n) t of
      None \<Rightarrow> None
      | Some ln' \<Rightarrow> Some (YulForLoop x1 x2 x3 (take n l @ ln' # drop (n+1) l))))"
| "yul_statement_update f (YulSwitch ce cl) (n)#t =
    (if length cl < cn then None
     else (case cl ! cn of (YulSwitchCase e l) \<Rightarrow>
       (if length l < n then None
        else (case yul_statement_update f (l!n) t of
          None \<Rightarrow> None
          | Some ln' \<Rightarrow>
            Some (YulSwitch ce (take cn cl @ 
                               (YulSwitchCase e (take n l @ ln' # drop (n+1) l)) #
                               (drop (cn +1) cl)))))))"
| "yul_statement_update _ _ _ = None"

end
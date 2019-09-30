module Main

{-
To write these functions in vim:
\d to make a template definition :addclause
\c over a variable to do case analysis on that variable :casesplit
\o to fill in a hole with the 'obvious' value

\m adds the missing cases for the name at the cursor :addmissing
\w adds a with clause :makewith

\o invokes a proof search to solve the hole under the
cursor (using :proofsearch).
\p invokes a proof search with additional hints to solve the hole

\t displays the type of the (globally visible) name under the
\e prompts for an expression to evaluate.
\r reloads and type checks the buffer.
-}

data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

%name Vect xs,ys,zs

append : Vect n a -> Vect m a -> Vect (n + m) a
append xs ys = ?append_rhs1

{-
Try to write this using the interactive tools alone:
append [] ys = ys
append (x :: xs) ys = x :: append xs ys
-}

vZipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c

{-
Try to write this using the interactive tools alone:
vZipWith f [] [] = []
vZipWith f (x :: xs) (y :: ys) = f x y :: vZipWith f xs ys
-}

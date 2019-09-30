module main

main : IO ()
main = putStrLn "oh boy"

even : Nat -> Bool
even Z = True
even (S Z) = False
even (S (S k)) = even k

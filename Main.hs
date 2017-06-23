import InhabTree

inhabTreeWrapper :: String -> String -> [Expr]
inhabTreeWrapper typeString countString = if null countString 
    then result 
    else take (read countString) result where
    result = inhabTree0 (read typeString)

main = do
    putStrLn "Please, enter the type to inhabit:"
    input <- getLine
    putStrLn "Please, enter the desired number of terms \nto limit the result with (leave blank if you want all):"
    count <- getLine
    print $ inhabTreeWrapper input count

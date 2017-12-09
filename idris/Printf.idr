module Printf
%default total

data Format =
	  FInt Format
	| FString Format
	| SimpleChar Char Format
	| End

format_of_string : String -> Format
format_of_string str = lok_format_of_string (unpack str) where
	lok_format_of_string : List Char -> Format
	lok_format_of_string ('%' :: 'd' :: tl) = FInt (lok_format_of_string tl)
	lok_format_of_string ('%' :: 's' :: tl) = FString (lok_format_of_string tl)
	lok_format_of_string (c :: tl) = SimpleChar c (lok_format_of_string tl)
	lok_format_of_string [] = End

printf_type_of_format : Format -> Type
printf_type_of_format (FInt other) = Int -> printf_type_of_format other
printf_type_of_format (FString other) = String -> printf_type_of_format other
printf_type_of_format (SimpleChar c other) = printf_type_of_format other
printf_type_of_format End = String

create_printf : (format : Format) -> String -> printf_type_of_format format
create_printf (FInt other) result = take_int where
	take_int : Int -> printf_type_of_format other
	take_int arg = create_printf other (result ++ show arg)
create_printf (FString other) result = take_string where
	take_string : String -> printf_type_of_format other
	take_string arg = create_printf other (result ++ arg)
create_printf (SimpleChar c other) result = create_printf other (result ++ singleton c)
create_printf End result = result

printf : (str : String) -> printf_type_of_format (format_of_string str)
printf str = create_printf (format_of_string str) ""

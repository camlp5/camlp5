(* camlp5r *)

value keywords = ["!";
	"!+";
	"!-";
	"!=";
	"#";
	"%";
	"&";
	"&&";
	"'";
	"(";
	")";
	"*";
	"**";
	"*.";
	"+";
	"+!";
	"+.";
	"+=";
	",";
	"-";
	"-!";
	"-.";
	"->";
	".";
	"..";
	"/";
	"/.";
	":";
	"::";
	":=";
	":>";
	":]";
	";";
	"<";
	"<=";
	"<>";
	"=";
	"==";
	">";
	">=";
	">}";
	"?";
	"?=";
	"@";
	"[";
	"[%";
	"[%%";
	"[:";
	"[@";
	"[@@";
	"[@@@";
	"[|";
	"]";
	"^";
	"_";
	"`";
	"alias";
	"and";
	"as";
	"asr";
	"assert";
	"class";
	"constraint";
	"declare";
	"do";
	"downto";
	"else";
	"end";
	"exception";
	"external";
	"for";
	"fun";
	"functor";
	"if";
	"in";
	"include";
	"inherit";
	"initializer";
	"land";
	"lazy";
	"let";
	"lor";
	"lsl";
	"lsr";
	"lxor";
	"match";
	"method";
	"mod";
	"module";
	"mutable";
	"new";
	"nonrec";
	"object";
	"of";
	"open";
	"parser";
	"private";
	"rec";
	"sig";
	"struct";
	"then";
	"to";
	"try";
	"type";
	"value";
	"virtual";
	"when";
	"where";
	"while";
	"with";
	"{";
	"{<";
	"|";
	"|]";
	"||";
	"}";
	"~";
	"~-";
	"~-."];
value keywords_hash = Hashtbl.create 23 ;
List.iter (fun k -> Hashtbl.add keywords_hash k k) keywords ;

%option yylineno
%pointer

%{
    #include <cstdlib>
    #include <cstring>
    #include <string>
    #include "ast.hpp"
    #include "parser.hpp"

    void yyerror(const char *);
%}

/** WRITE ME:
 *  Put any definitions you need here. Add your own regular expressions
 *  below for ALL tokens defined in the manual. You can choose not to use
 *  definitions here.
 */

/* HERE */

%x comment

/** The example below is very simple, but it shows almost everything you will
 *  need to do for this first part. The syntax is as follows:
 *
 *  regular_expression      {  c code  }
 *
 * The lexer will try to match each regular expression. When it does it will
 * execute the corresponding C code.
*/

%%
"integer"				{return T_INTTYPE;}
"intptr"				{return T_INTPTRTYPE;}
"string"				{return T_STRINGTYPE;}
"charptr"				{return T_CHARPTRTYPE;}
"char"					{return T_CHARTYPE;}
"true"					{ yylval.u_base_int = 1; return T_TRUE;}
"false"					{ yylval.u_base_int = 0; return T_FALSE;}
"boolean"				{return T_BOOLTYPE;}
"if"					{return T_IF;}
"else"					{return T_ELSE;}
"while"					{return T_WHILE;}
"var"					{return T_VAR;}
"procedure"				{return T_PROCEDURE;}
"null"					{return T_NULLTYPE;}
"return"				{return T_RETURN;}
"="						{return T_ASSIGN;}
"!="					{return T_NOTEQUAL;}
"||"					{return T_OR;}
"&&"					{return T_AND;}
"!"						{return T_NOT;}
"=="					{return T_ISEQUAL;}
">"						{return T_GREATERTHAN;}
">="					{return T_GREATERTHANOREQ;}
"<"						{return T_LESSTHAN;}
"<="					{return T_LESSTHANOREQ;}
0|[1-9][0-9]*			{
							yylval.u_base_int = (int)strtol(yytext, 0, 10);
							return T_INTEGER_DEC;
						}
0[xX][0-9a-fA-F]+		{
							yylval.u_base_int = std::stoi(strdup(yytext),
														  nullptr,
														  16); 
							return T_INTEGER_HEX;
						}
[0-1]+[b]				{
							yylval.u_base_int = std::stoi(strdup(yytext),
														  nullptr,
														  2);
							return T_INTEGER_BIN;
						}
0[0-7]+					{
							yylval.u_base_int = std::stoi(strdup(yytext),
														  nullptr,
														  8);
							return T_INTEGER_OCT;
						}
[\*\(\)\.\+\-\%\;\:\{\}\,\^\/\[\]\&\|]  { return *yytext; }

[\"][^\"]*[\"] /* " */	{
							yytext++; 
							yytext[strlen(yytext)-1] = 0;
							yylval.u_base_charptr = strdup(yytext); 
						 	return T_STRING;
						} 
[\'][[:print:]]?[\'] /* ' */	{
									yytext++; 
									yytext[strlen(yytext)-1] = 0;
									yylval.u_base_int = int(*yytext); 
									return T_CHAR;
								} 
[a-zA-Z][a-zA-Z0-9_]*  {yylval.u_base_charptr = strdup(yytext); return T_ID1;}	
[ \t\n]             	; /* skip whitespace */

"/%" BEGIN( comment );
<comment>[^%]*		
<comment>"%"+[^%/\n]*  	
<comment>"%"+"/" {BEGIN( INITIAL );}
<comment><<EOF>> {yyerror("DANGLING COMMENT");}
[.]* 	{yyerror((char *) "invalid character");}

%%

/** You shall not pass!
 *  You should not  have to do or edit anything past this.
 */

int yywrap(void) {
    return 1;
}

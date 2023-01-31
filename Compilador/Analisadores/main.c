#include "globals.h"
#include "util.h"
#include "parse.h"
#include "analyze.h"


FILE *yyin;
FILE *source;

TreeNode *syntaxTree;
int numlinha = 1;
int iniciolinha = 1;

int Error = FALSE;

TokenType getToken();
void Scanner();

int main()
{
    FILE *f_out = fopen("outParser.output", "w+");
    char path[100];
    int flag;
    
    printf("Caminho para o .txt que vai ser utilizado: ");
        
    flag = scanf("%s",path);

    if(flag){
    	printf("\nCaminho escrito!\n");
    }
    source = fopen(path, "r");
    yyin = source;

    printf("\nCompilador C-");
    printf("\n------------------------------------------------------\n");

    printf("\nRealizando Scanner...\n");
    Scanner();

    if(!Error){
        printf("\nScanner concluido.\n");

        rewind(yyin);
        rewind(source);
        numlinha = 1;
        iniciolinha = 1;

        printf("\nGerando Arvore Sintatica...\n");
        syntaxTree = parse();
    
        if (!Error){
            printf("\nArvore Sintatica gerada com sucesso, salva em OutParser.\n");

            printf("\nConstruindo Tabela de Simbolos...\n");
            buildSymtab(syntaxTree);
            if (!Error){
                printf("\nTabela de Simbolos construida com sucesso, salva em OutAnalyze.\n");
                printf("\nChecando semantica...\n");
                typeCheck(syntaxTree);

		if (!Error){
			printf("\nCodigo semanticamente correto.\n");
			printTree(syntaxTree, f_out);
		}
		else{
			
		}
            }
        }
    }
    fclose(f_out);
    fclose(source);

    return 0;
}

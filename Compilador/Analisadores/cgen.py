from anytree import Node

nextDec = 0
label = 0
temp = 0
flag = 0
globalSize = 0
tempAux = ""
tempAux2 = ""


def cGen(filename):
    '''
    This part of the code build the tree in python
    '''

    def _recurse_tree(pare, depth, source):
        last_line = source.readline().rstrip()

        while last_line:
            tabs = last_line.count('\t')
            if tabs < depth:
                break
                
            node_name = last_line.strip()
            if tabs >= depth:
                node = Node(node_name, parent=pare)
                last_line = _recurse_tree(node, tabs+1, source)
        
        return last_line

    '''
    This part of the code build the code generator python
    '''
    def newTemp():
        global temp
        temp = (temp + 1)%17

    def genStatement(tree,quadList):
        name = tree.name.split()[0]
        global label
        global flag
        global temp
        global tempAux
        global tempAux2
        global globalSize

        if name == 'If':
            if(len(tree.children) > 0):
                cGen(tree.children[0],quadList)
            arg1 = tempAux
            arg2 = f"L{label}"
            label = label + 1
            aux1 = arg2
            arg3 = "-"
            quadList.append(f"IFF {arg1} {arg2} {arg3}")

            count = 0

            # If true
            if(len(tree.children) > 1):
                while(count < int(tree.name.split()[1])):
                    count = count + 1
                    cGen(tree.children[count],quadList)
                    
            # Else not null
            if(int(tree.name.split()[2]) > 0):
                arg1 = f"L{label}"
                label = label + 1
                aux2 = arg1
                arg2 = "-"
                arg3 = "-"
                quadList.append(f"GOTO {arg1} {arg2} {arg3}")

            a = count

            # If false
            if(int(tree.name.split()[2]) > 0):
                arg1 = aux1
                arg2 = "-"
                arg3 = "-"
                quadList.append(f"LABEL {arg1} {arg2} {arg3}")
                while(count < (int(tree.name.split()[2]) + a)):
                    count = count + 1
                    cGen(tree.children[count],quadList)
                    
            # If saída
            if(int(tree.name.split()[2]) > 0):
                arg1 = aux2
            else:
                arg1 = aux1
            
            arg2 = "-"
            arg3 = "-"
            quadList.append(f"LABEL {arg1} {arg2} {arg3}")


        elif name == 'Atribuicao':
            if(len(tree.children) > 0):
                if(tree.children[0].name.split()[0] == 'Vetor:' ):
                    flag = 1
                cGen(tree.children[0],quadList)
            arg1 = tempAux
            if(len(tree.children) > 1):
                if(tree.children[0].name.split()[0] == 'Vetor:' and tree.children[1].name.split()[0] == 'Vetor:'):
                    flag = 1
                cGen(tree.children[1],quadList)
            arg2 = tempAux
            arg3 = "-"
            quadList.append(f"ASSIGN {arg1} {arg2} {arg3}")

            if(flag == 2):
                arg3 = tempAux2
                flag = 0
            
            aux1 = arg1
            if(tree.children[0].name.split()[0] == 'Vetor:' and tree.children[1].name.split()[0] == 'Vetor:'):
                if(len(tree.children) > 0):
                    arg1 = tree.children[0].name.split()[1]
                arg2 = aux1
                
                m = arg3[0:2]
                n = arg3[2:4]
                
                if(m == "$t"):
                    h = int(n)
                    h = h - 2
                    arg3 = f"{m}{h}"

                quadList.append(f"STORE {arg1} {arg2} {arg3}")
                arg3 = f"{m}{n}"

            else:    
                if(len(tree.children) > 0):
                    arg1 = tree.children[0].name.split()[1]
                arg2 = aux1
                quadList.append(f"STORE {arg1} {arg2} {arg3}")
            

        elif name == 'While':
            arg1 = f"L{label}"
            label = label + 1
            aux1 = arg1
            arg2 = "-"
            arg3 = "-"
            quadList.append(f"LABEL {arg1} {arg2} {arg3}")

            if(len(tree.children) > 0):
                cGen(tree.children[0],quadList)
            arg1 = tempAux
            arg2 = f"L{label}"
            label = label + 1
            aux2 = arg2
            arg3 = "-"
            quadList.append(f"IFF {arg1} {arg2} {arg3}")
            
            
            for i in range(1,len(tree.children)):
                cGen(tree.children[i],quadList)
            arg1 = aux1
            arg2 = "-"
            arg3 = "-"
            quadList.append(f"GOTO {arg1} {arg2} {arg3}")

            arg1 = aux2
            arg2 = "-"
            arg3 = "-"
            quadList.append(f"LABEL {arg1} {arg2} {arg3}")

        elif name == 'Variavel:':
            arg1 = tree.name.split()[1]
            arg2 = tree.name.split()[2]
            if tree.name.split()[3] == '2':
                arg3 = tree.name.split()[4]
                quadList.append(f"ALLOC {arg1} {arg2} {arg3}")
                if arg2 == "global": 
                    globalSize = int(tree.name.split()[4]) + globalSize
            else:
                arg3 = "-"
                quadList.append(f"ALLOC {arg1} {arg2} {arg3}")
                if arg2 == "global":
                    globalSize = 1 + globalSize

        elif name == 'Funcao:':
            if (tree.parent.name.split()[1] == 'inteiro'):
                arg1 = 'int'
            else:
                arg1 = 'void'
            arg2 = tree.name.split()[1]
            arg3 = '-'
            quadList.append(f"FUN {arg1} {arg2} {arg3}")
            for child in tree.children:
                cGen(child,quadList)

            arg1 = arg2
            arg2 = '-'
            arg3 = '-'
            quadList.append(f"END {arg1} {arg2} {arg3}")

        elif name == 'Chamada':
            for child in tree.children:
                cGen(child,quadList)
                if(temp == 0):
                    i = 16
                else:    
                    i = temp - 1
                quadList.append(f"ARG $t{i} - -")

            tempAux = f"$t{temp}"
            newTemp()
            arg1 = tempAux
            arg2 = tree.name.split()[3]
            arg3 = len(tree.children)
            quadList.append(f"CALL {arg1} {arg2} {arg3}")

        elif name == 'Return':
            if(len(tree.children) > 0):
                cGen(tree.children[0],quadList)
            arg1 = tempAux
            arg2 = '-'
            arg3 = '-'
            quadList.append(f"RET {arg1} {arg2} {arg3}")
        
        elif name == 'Parametro:':
            if tree.name.split()[3] == '1':
                arg1 = "int"
            else:
                arg1 = "int[]"
            arg2 = tree.name.split()[1]
            arg3 = tree.name.split()[2]
            quadList.append(f"PARAM {arg1} {arg2} {arg3}")



    def genExpression(tree,quadList):
        name = tree.name.split()[0]
        global label
        global flag
        global temp
        global tempAux
        global tempAux2

        if name == 'Operacao:':
            if(len(tree.children) > 0):
                cGen(tree.children[0],quadList)
            arg2 = tempAux
            if(len(tree.children) > 1):
                cGen(tree.children[1],quadList)
            arg3 = tempAux
            tempAux = f"$t{temp}"
            newTemp()
            arg1 = tempAux

            if tree.name.split()[-1] == '+':
                quadList.append(f"ADD {arg1} {arg2} {arg3}")
            
            elif tree.name.split()[-1] == '-':
                quadList.append(f"SUB {arg1} {arg2} {arg3}")
            
            elif tree.name.split()[-1] == '*':
                quadList.append(f"MUL {arg1} {arg2} {arg3}")
            
            elif tree.name.split()[-1] == '/':
                quadList.append(f"DIV {arg1} {arg2} {arg3}")
            
            elif tree.name.split()[-1] == '<': 
                quadList.append(f"LT {arg1} {arg2} {arg3}")
            
            elif tree.name.split()[-1] == '<=': 
                quadList.append(f"LET {arg1} {arg2} {arg3}")
            
            elif tree.name.split()[-1] == '>': 
                quadList.append(f"GT {arg1} {arg2} {arg3}")
            
            elif tree.name.split()[-1] == '>=':
                quadList.append(f"GET {arg1} {arg2} {arg3}")
            
            elif tree.name.split()[-1] == '==':
                quadList.append(f"EQ {arg1} {arg2} {arg3}")
            
            elif tree.name.split()[-1] == '!=': 
                quadList.append(f"NEQ {arg1} {arg2} {arg3}")
            

        elif name == 'Constante:':
            tempAux = f"$t{temp}"
            newTemp()
            arg1 = tempAux
            arg2 = tree.name.split()[1]
            arg3 = "-"
            quadList.append(f"LOAD {arg1} {arg2} {arg3}")
        
        elif name == 'ID:':
            tempAux = f"$t{temp}"
            newTemp()
            arg1 = tempAux
            arg2 = tree.name.split()[1]
            arg3 = "-"
            quadList.append(f"LOAD {arg1} {arg2} {arg3}")

        elif name == 'Vetor:':
            if(len(tree.children) > 0):
                cGen(tree.children[0],quadList)
            
            arg3 = tempAux
            if (flag == 1):
                tempAux2 = arg3
                flag = 2
            
            tempAux = f"$t{temp}"
            newTemp()
            arg1 = tempAux
            arg2 = tree.name.split()[1]
            quadList.append(f"LOAD {arg1} {arg2} {arg3}")

        elif name == 'Tipo:':
            if(len(tree.children) > 0):
                cGen(tree.children[0],quadList)
        
        
    def cGen(tree,quadList):

        if (tree != None):
            global nextDec 
            nextDec = nextDec + 1
            name = tree.name.split()[0]
            statem = ['If','Atribuicao','While','Variavel:','Funcao:','Chamada','Return','Parametro:']
            expre = ['Operacao:','Constante:','ID:','Vetor:','Index','Tipo:']
            if name in statem:
                genStatement(tree,quadList)
            elif name in expre:
                genExpression(tree,quadList)
        
        nextDec = nextDec - 1
        if (nextDec == 0):
            if(len(tree.children) > 1):
                cGen(tree.children[1],quadList)

    inFile = open(filename)
    last_line = inFile.readline().rstrip()
    root = Node(last_line.strip())
    _recurse_tree(root, 0, inFile)

    quadruLista = []
    cGen(root,quadruLista)

    quadruLista.append("HLT - - -")

    arquivo = open("cgen.txt", "a")
    for inst in quadruLista:
        arquivo.write(f"{inst}\n")

    quadruLista.append(globalSize)
    
    return quadruLista


if __name__ == '__main__':
    fileName = "outParser.output" 
    cGenList = cGen(fileName)
    for inst in cGenList:
        print(inst)




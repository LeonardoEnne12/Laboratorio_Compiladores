from cgen import cGen

class HashTable:
    def __init__(self, name, scope, typeID, typeData, paramQt, loc, size,instLine):
        self.Name = name
        self.Scope = scope
        self.TypeID = typeID
        self.TypeData = typeData
        self.ParamQt = paramQt
        self.Loc = loc
        self.Size = size
        self.InstLine = instLine
        self.NumLine = []

class Instru:
    def __init__(self, instr, rd, r1, r2, im, line,lineKind, label ):
        self.InstrucKind = instr
        self.Rd = rd
        self.R1 = r1
        self.R2 = r2
        
        self.Im = im
        self.Line = line
        self.LineKind = lineKind # 0 se for instrução e 1 se for label
        self.Label = label

line = 0                         # Numero da linha da instrucao Assembly
argRegNum = 0                    # Numero do registrador de argumento
argReg = ""                      # Seleciona o registrador de argumento
isPos = 0                        # Local do stack na memoria
glVarLoc = 0                     # Onde colocar variaveis globais na memoria
ctScp = ""                       # Escopo atual alterado uma vez que a quadrupla FUN aparece
argCounter = 0                   # Conta quantos argumentos ainda faltam para se guardar na memoria




def assembly(filename,filenameTable):

    def hashTable(source):
        table = []
        with open(source) as file:
            i = 0
            for line in file:
                if(i > 3):
                    splitedLine = line.split() 
                    lineHash = HashTable(splitedLine[0], splitedLine[1], splitedLine[2], splitedLine[3], 
                    splitedLine[4], splitedLine[5], splitedLine[6], splitedLine[7])
                    
                    j = 8

                    while(j < len(splitedLine)):
                        lineHash.NumLine.append(int(splitedLine[j]))
                        j = j + 1
    
                    table.append(lineHash)
                else:
                    i = i + 1
            
        return table

    def memoryInsert(table, name, scope, loca, instlin):
    
        for list in table:
            if (list.Name == name and list.Scope == scope):
                list.Loc = loca            
                list.InstLine = instlin

        
        
    def paramQt(table, name, scope):
        counter = 0
        for list in table:
            if (list.Name == name and list.Scope == scope):
                l = list
                counter = 0
                break
            else:
                counter = 1 

        if( counter == 1 ):
            return -1
        
        else:
            return int(l.ParamQt)

    def loc(table, name, scope):
        counter = 0
        for list in table:
            if (list.Name == name and list.Scope == scope):
                l = list
                counter = 0
                break
            else:
                counter = 1 

        if( counter == 1 ):
            return -1
        
        else:
            return int(l.Loc)

    def size(table, name, scope):
        counter = 0
        for list in table:
            if (list.Name == name and list.Scope == scope):
                l = list
                counter = 0
                break
            else:
                counter = 1 

        if( counter == 1 ):
            return -1
        
        else:
            return int(l.Size)

    def typeData(table, name, scope):
        counter = 0
        for list in table:
            if (list.Name == name and list.Scope == scope):
                l = list
                counter = 0
                break
            else:
                counter = 1 

        if( counter == 1 ):
            return "NULL"
        
        else:
            return l.TypeData

    def lookup(table, name, scope):
        for list in table:
            if (list.Name == name and list.Scope == scope):
                counter = 0
                break
            else:
                counter = 1 

        if( counter == 1 ):
            return 0
        
        else:
            return 1

    def LOAD(quad,assemInstr,reglist,table):
        global line
        global ctScp

        if(quad.split()[2].isdigit()):
            instruAss = Instru("ADDI" , quad.split()[1] , "$zero" , "0" , int(quad.split()[2]) , line , 0 , "")
            assemInstr.append(instruAss)
            line = line + 1  

        else:
            if(lookup(table, quad.split()[2], "global" ) == 1):
                l = loc(table, quad.split()[2], "global")
                if(quad.split()[3] != "-"):
                    instruAss = Instru("LOAD" , quad.split()[1] , quad.split()[3] , "0" , l , line , 0 , "")
                    assemInstr.append(instruAss)

                    if (quad.split()[3] in reglist):
                        reglist.remove(quad.split()[3])

                else:

                    for tab in table:
                        if(quad.split()[2] == tab.Name and tab.Scope == ctScp):
                            for t in table:
                                if(quad.split()[2] == t.Name and t.Scope == "global"):
                                    tab.Size = t.Size

                    if(size(table, quad.split()[2],ctScp) > 1):
                        instruAss = Instru("ADDI" , quad.split()[1] , "$zero" , "0" , l , line , 0 , "")
                        assemInstr.append(instruAss)
                    else:
                        instruAss = Instru("LOAD" , quad.split()[1] , "$zero" , "0" , l , line , 0 , "")
                        assemInstr.append(instruAss)

                line = line + 1

            else:
                l = loc(table, quad.split()[2], ctScp)
                if(quad.split()[3] != "-"):
                    if(typeData(table,quad.split()[2],ctScp) == "vetorarg"):
                        
                        instruAss = Instru("LOAD" , quad.split()[1] , "$sp" , "0" , l , line , 0 , "")
                        assemInstr.append(instruAss)
                        line = line + 1

                        instruAss = Instru("ADD" , quad.split()[1] , quad.split()[1] , quad.split()[3] , 0 , line , 0 , "")
                        assemInstr.append(instruAss)
                        line = line + 1

                        instruAss = Instru("LOAD" , quad.split()[1] , quad.split()[1] , "0" , 0 , line , 0 , "")
                        assemInstr.append(instruAss)
                    else:

                        instruAss = Instru("ADD" , quad.split()[3] , quad.split()[3] , "$sp" , 0 , line , 0 , "")
                        assemInstr.append(instruAss)
                        line = line + 1

                        instruAss = Instru("LOAD" , quad.split()[1] , quad.split()[3] , "0" , l , line , 0 , "")
                        assemInstr.append(instruAss)

                    if (quad.split()[3] in reglist):
                        reglist.remove(quad.split()[3])

                else:
                    
                    if(size(table,quad.split()[2],ctScp) > 1 and typeData(table, quad.split()[2], ctScp) != "vetorarg"):
                        instruAss = Instru("ADDI" , quad.split()[1] , "$sp" , "0" , l , line , 0 , "")
                        assemInstr.append(instruAss)

                    else:
                        instruAss = Instru("LOAD" , quad.split()[1] , "$sp" , "0" , l , line , 0 , "")
                        assemInstr.append(instruAss)

                line = line + 1

        reglist.append(quad.split()[1])

    def STORE(quad,assemInstr,reglist,table):
        global line
        global ctScp

        if(lookup(table,quad.split()[1],"global") == 1):
            l = loc(table,quad.split()[1],"global")
            if(quad.split()[3] != "-"):
                instruAss = Instru("STORE" , quad.split()[2] , quad.split()[3] , "0" , l , line , 0 , "")
                assemInstr.append(instruAss)

                if (quad.split()[3] in reglist):
                        reglist.remove(quad.split()[3])

            else:
                instruAss = Instru("STORE" , quad.split()[2] , "$zero" , "0" , l , line , 0 , "")
                assemInstr.append(instruAss)

            line = line + 1

        else:
            l = loc(table,quad.split()[1],ctScp)
            if(quad.split()[3] != "-"):
                if(typeData(table,quad.split()[1],ctScp) == "vetorarg"):
                    instruAss = Instru("LOAD" , "$ad" , "$sp" , "0" , l , line , 0 , "")
                    assemInstr.append(instruAss)
                    line = line + 1

                    instruAss = Instru("ADD" , "$ad" , "$ad" , quad.split()[3] , 0 , line , 0 , "")
                    assemInstr.append(instruAss)
                    line = line + 1

                    instruAss = Instru("STORE" , quad.split()[2] , "$ad" , "0" , 0 , line , 0 , "")
                    assemInstr.append(instruAss)
                
                else:
                    instruAss = Instru("ADD" , quad.split()[3] , quad.split()[3] , "$sp" , 0 , line , 0 , "")
                    assemInstr.append(instruAss)
                    line = line + 1

                    instruAss = Instru("STORE" , quad.split()[2] , quad.split()[3] , "0" , l , line , 0 , "")
                    assemInstr.append(instruAss)
                
                if (quad.split()[3] in reglist):
                    reglist.remove(quad.split()[3])
            
            else:
                instruAss = Instru("STORE" , quad.split()[2] , "$sp" , "0" , l , line , 0 , "")
                assemInstr.append(instruAss)
            
            line = line + 1
        
        if (quad.split()[2] in reglist):
            reglist.remove(quad.split()[2])

    def CALL(quad,assemInstr,reglist,table):
        global argRegNum
        global line
        global argReg
        global sPos
        global ctScp

        if(quad.split()[2] == "output"):
            instruAss = Instru("OUT" , "$a0" , "0" , "0" , 0 , line , 0 , "")
            assemInstr.append(instruAss)
            line = line + 1
            argRegNum = 0  
            argReg = "$a0"            
        
        elif(quad.split()[2] == "input"):
            instruAss = Instru("IN" , quad.split()[1] , "0" , "0" , 0 , line , 0 , "")
            assemInstr.append(instruAss)
            line = line + 1            
            reglist.append(quad.split()[1])

        else:
            for reg in reglist:
                instruAss = Instru("STORE" , reg , "$sp" , "0" , sPos , line , 0 , "")
                assemInstr.append(instruAss)
                line = line + 1
                sPos = sPos + 1  

            if(ctScp != "main"):
                instruAss = Instru("STORE" , "$ra" , "$sp" , "0" , sPos , line , 0 , "")
                assemInstr.append(instruAss)
                line = line + 1
                sPos = sPos + 1 

            instruAss = Instru("ADDI" , "$sp" , "$sp" , "0" , sPos , line , 0 , "")
            assemInstr.append(instruAss)
            line = line + 1
            argRegNum = 0  
            argReg = "$a0"

            instruAss = Instru("JAL" , "0" , "0" , 0 , sPos , line , 0 , quad.split()[2])
            assemInstr.append(instruAss)
            line = line + 1

            instruAss = Instru("SUBI" , "$sp" , "$sp" , 0 , sPos , line , 0 , "")
            assemInstr.append(instruAss)
            line = line + 1

            if(ctScp != "main"):
                sPos = sPos - 1
                instruAss = Instru("LOAD" , "$ra" , "$sp" , "0" , sPos , line , 0 , "")
                assemInstr.append(instruAss)
                line = line + 1

            for reg in reversed(reglist):
                sPos = sPos - 1
                instruAss = Instru("LOAD" , reg , "$sp" , "0" , sPos , line , 0 , "")
                assemInstr.append(instruAss)
                line = line + 1
            
            dataType =  typeData(table, quad.split()[2], "global")
            if(dataType == "inteiro"):
                instruAss = Instru("ADD" , quad.split()[1] , "$v0" , "$zero" , 0 , line , 0 , "")
                assemInstr.append(instruAss)
                line = line + 1
                reglist.append(quad.split()[1])

    def FUN(quad,assemInstr,table):
        global argRegNum
        global line
        global argReg
        global sPos   
        global ctScp
        global argCounter
        b = line
        memoryInsert(table,quad.split()[2], "global", -1, b)
        instruAss = Instru("0", "0", "0", "0", 0, line, 1, quad.split()[2])
        assemInstr.append(instruAss)
        sPos = 0
        ctScp = quad.split()[2]
        argRegNum = 0  
        argReg = "$a0"
        argCounter = paramQt(table, quad.split()[2], "global");   
    

    def PARAM(quad,assemInstr,table):
        global argRegNum
        global line
        global argReg
        global sPos   
        global argCounter

        memoryInsert(table,quad.split()[2], quad.split()[3], sPos, 0)
        instruAss = Instru("STORE" , argReg , "$sp" , "0" , sPos, line, 0 ,"")
        assemInstr.append(instruAss)
        sPos = sPos + 1
        line = line + 1
        argRegNum = argRegNum + 1
        argReg = f"$a{argRegNum}"
        argCounter = argCounter - 1
        if(argCounter == 0):
            argRegNum = 0  
            argReg = "$a0"


    def ARG(quad,assemInstr,reglist):
        global argRegNum
        global line
        global argReg   

        instruAss = Instru("ADD" , argReg , quad.split()[1] , "$zero" , 0, line, 0 ,"")
        assemInstr.append(instruAss)
        line = line + 1
        argRegNum = argRegNum + 1
        argReg = f"$a{argRegNum}"
        if (quad.split()[1] in reglist):
            reglist.remove(quad.split()[1])

    def ALLOC(quad,table):
        global sPos
        global glVarLoc   

        if(quad.split()[2] == "global"):
            memoryInsert(table,quad.split()[1], quad.split()[2], glVarLoc, 0)
            glVarLoc = glVarLoc + size(table, quad.split()[1],quad.split()[2])
        
        else:
            memoryInsert(table,quad.split()[1], quad.split()[2], sPos, 0)
            sPos = sPos + size(table, quad.split()[1],quad.split()[2])

    def RET(quad,assemInstr,reglist):
        global line   

        instruAss = Instru("ADD" , "$v0" , quad.split()[1] , "$zero" , 0, line, 0 ,"")
        assemInstr.append(instruAss)
        line = line + 1
        instruAss = Instru("JR" , "$ra" , "0" , "0" , 0, line, 0 ,"")
        assemInstr.append(instruAss)
        line = line + 1
        if (quad.split()[1] in reglist):
            reglist.remove(quad.split()[1])

    def END(quad,assemInstr):
        global line   

        if(quad.split()[1] != "main"):
            instruAss = Instru("JR" , "$ra" , "0" , "0" , 0, line, 0 ,"")
            assemInstr.append(instruAss)
            line = line + 1

    def ASSIGN(quad,assemInstr,reglist):
        global line   

        instruAss = Instru("ADD" , quad.split()[1] , quad.split()[2] , "$zero" , 0, line, 0 ,"")
        assemInstr.append(instruAss)
        line = line + 1
        if (quad.split()[2] in reglist):
            reglist.remove(quad.split()[2])

    def LABEL(quad,assemInstr,map):
        global line   

        l = quad.split()[1]
        map.append(f"{l} {line}")

        instruAss = Instru("0" , "0" , "0" , "0" , 0, line, 1 ,quad.split()[1])
        assemInstr.append(instruAss)

    def GOTO(quad,assemInstr):
        global line   

        instruAss = Instru("J" , "0" , "0" , "0" , 0, line, 0 ,quad.split()[1])
        assemInstr.append(instruAss)
        line = line + 1

    def IFF(quad,assemInstr,reglist):
        global line   

        instruAss = Instru("BEQ" , quad.split()[1] , "$zero" , "0" , 0, line, 0 ,quad.split()[2])
        assemInstr.append(instruAss)
        line = line + 1
        if (quad.split()[1] in reglist):
            reglist.remove(quad.split()[1])

    def ARITHMETIC(quad,assemInstr,reglist):
        global line    
 
        instruAss = Instru(quad.split()[0] , quad.split()[1] , quad.split()[2] , quad.split()[3] , 0, line, 0 ,"")
        assemInstr.append(instruAss)
        line = line + 1
        if (quad.split()[2] in reglist):
            reglist.remove(quad.split()[2])
        if (quad.split()[3] in reglist):    
            reglist.remove(quad.split()[3])
        reglist.append(quad.split()[1])

    def LT(quad,assemInstr,reglist):
        global line   

        instruAss = Instru("SLT" , quad.split()[1] , quad.split()[2] , quad.split()[3] , 0, line, 0 ,"")
        assemInstr.append(instruAss)
        line = line + 1
        if (quad.split()[2] in reglist):
            reglist.remove(quad.split()[2])
        if (quad.split()[3] in reglist):
            reglist.remove(quad.split()[3])
        reglist.append(quad.split()[1])

    def LET(quad,assemInstr,reglist):
        global line

        instruAss = Instru("SLET" , quad.split()[1] , quad.split()[2] , quad.split()[3] , 0, line, 0 ,"")
        assemInstr.append(instruAss)
        line = line + 1
        if (quad.split()[2] in reglist):
            reglist.remove(quad.split()[2])
        if (quad.split()[3] in reglist):
            reglist.remove(quad.split()[3])
        reglist.append(quad.split()[1])

    def GT(quad,assemInstr,reglist):
        global line

        instruAss = Instru("SGT" , quad.split()[1] , quad.split()[2] , quad.split()[3] , 0, line, 0 ,"")
        assemInstr.append(instruAss)
        line = line + 1
        if (quad.split()[2] in reglist):
            reglist.remove(quad.split()[2])
        if (quad.split()[3] in reglist):
            reglist.remove(quad.split()[3])
        reglist.append(quad.split()[1])

    def GET(quad,assemInstr,reglist):
        global line

        instruAss = Instru("SGET" , quad.split()[1] , quad.split()[2] , quad.split()[3] , 0, line, 0 ,"")
        assemInstr.append(instruAss)
        line = line + 1
        if (quad.split()[2] in reglist):
            reglist.remove(quad.split()[2])
        if (quad.split()[3] in reglist):
            reglist.remove(quad.split()[3])
        reglist.append(quad.split()[1])

    def EQ(quad,assemInstr,reglist,quadNext):
        global line

        instruAss = Instru("BNEQ" , quad.split()[2] , quad.split()[3] , "0" , 0, line, 0 ,quadNext.split()[2])
        assemInstr.append(instruAss)
        line = line + 1
        if (quad.split()[2] in reglist):
            reglist.remove(quad.split()[2])
        if (quad.split()[3] in reglist):
            reglist.remove(quad.split()[3])

    def NEQ(quad,assemInstr,reglist,quadNext):
        global line

        instruAss = Instru("BEQ" , quad.split()[2] , quad.split()[3] , "0" , 0, line, 0 ,quadNext.split()[2])
        assemInstr.append(instruAss)
        line = line + 1
        if (quad.split()[2] in reglist):
            reglist.remove(quad.split()[2])
        if (quad.split()[3] in reglist):
            reglist.remove(quad.split()[3])

    def HLT(assemInstr):
        global line

        instruAss = Instru("HLT" , "0" , "0" , "0" , 0, line, 0 ,"")
        assemInstr.append(instruAss)
        line = line + 1

    def assemGenerator(cGenQuad,assemInstr,unUsReg,glSize,table,labMap):
        global sPos
        global line
        global argCounter

        sPos = glSize

        instruAss = Instru("ADDI","$sp", "$zero", "" ,sPos, line,0,"")
        assemInstr.append(instruAss)
        line = line + 1
        instruAss = Instru("J","", "", "" ,0, line,0,"main")
        assemInstr.append(instruAss) 
        line = line + 1  

        i = 0
        while i < len(cGenQuad):
            quad = cGenQuad[i]
            if(quad.split()[0] == "FUN"):
                FUN(quad,assemInstr,table)
            elif(quad.split()[0] == "ARG"):
                ARG(quad,assemInstr,unUsReg)
            elif(quad.split()[0] == "PARAM"):
                PARAM(quad,assemInstr,table)
            elif(quad.split()[0] == "ALLOC"):
                ALLOC(quad,table)
            elif(quad.split()[0] == "CALL"):
                CALL(quad,assemInstr,unUsReg,table)
            elif(quad.split()[0] == "RET"):
                RET(quad,assemInstr,unUsReg)
            elif(quad.split()[0] == "END"):
                END(quad,assemInstr)
            elif(quad.split()[0] == "LOAD"):
                LOAD(quad,assemInstr,unUsReg,table)
            elif(quad.split()[0] == "STORE"):
                STORE(quad,assemInstr,unUsReg,table)
            elif(quad.split()[0] == "ASSIGN"):
                ASSIGN(quad,assemInstr,unUsReg)
            elif(quad.split()[0] == "LABEL"):
                LABEL(quad,assemInstr,labMap)
            elif(quad.split()[0] == "GOTO"):
                GOTO(quad,assemInstr)
            elif(quad.split()[0] == "IFF"):
                IFF(quad,assemInstr,unUsReg)
            elif(quad.split()[0] == "ADD" or quad.split()[0] == "SUB"):
                ARITHMETIC(quad,assemInstr,unUsReg)
            elif(quad.split()[0] == "MUL" or quad.split()[0] == "DIV"):
                ARITHMETIC(quad,assemInstr,unUsReg)
            elif(quad.split()[0] == "LT"):
                LT(quad,assemInstr,unUsReg)
            elif(quad.split()[0] == "LET"):
                LET(quad,assemInstr,unUsReg)
            elif(quad.split()[0] == "GT"):
                GT(quad,assemInstr,unUsReg)
            elif(quad.split()[0] == "GET"):
                GET(quad,assemInstr,unUsReg)
            elif(quad.split()[0] == "EQ"):
                EQ(quad,assemInstr,unUsReg,cGenQuad[i+1])
                i = i + 1
            elif(quad.split()[0] == "NEQ"):
                NEQ(quad,assemInstr,unUsReg,cGenQuad[i+1])
                i = i + 1
            elif(quad.split()[0] == "HLT"):
                HLT(assemInstr)
            
            i = i + 1


    cGenList = cGen(filename)

    table = hashTable(filenameTable)

    globalSize = cGenList[-1]

    del cGenList[-1]

    assemList = []
    unUsedReg = []
    labelMap = []
    
    assemGenerator(cGenList,assemList,unUsedReg,globalSize,table,labelMap)

    arquivo = open("assembly.txt", "a")
    for inst in assemList:
        if (inst.LineKind == 0):
            if(inst.InstrucKind == "ADD" or inst.InstrucKind == "SUB" or inst.InstrucKind == "MUL" or inst.InstrucKind == "DIV"
                or inst.InstrucKind == "AND" or inst.InstrucKind == "OR" or inst.InstrucKind == "XOR" or inst.InstrucKind == "SLT"
                or inst.InstrucKind == "SGT" or inst.InstrucKind == "SLET" or inst.InstrucKind == "SGET" or inst.InstrucKind == "SET"):
                arquivo.write(f"{inst.Line} {inst.InstrucKind}, {inst.Rd}, {inst.R1}, {inst.R2}\n")
            
            
            elif(inst.InstrucKind == "NOT" or inst.InstrucKind == "SR" or inst.InstrucKind == "SL"):
                arquivo.write(f"{inst.Line} {inst.InstrucKind}, {inst.Rd}, {inst.R1}\n")

            elif(inst.InstrucKind == "JR" or inst.InstrucKind == "IN" or inst.InstrucKind == "OUT"):
                arquivo.write(f"{inst.Line} {inst.InstrucKind}, {inst.Rd}\n")

            elif(inst.InstrucKind == "ADDI" or inst.InstrucKind == "SUBI" or inst.InstrucKind == "LOAD" or
                inst.InstrucKind == "STORE"):
                arquivo.write(f"{inst.Line} {inst.InstrucKind}, {inst.Rd}, {inst.R1}, {inst.Im}\n")

            elif(inst.InstrucKind == "BEQ" or inst.InstrucKind == "BNEQ"):
                arquivo.write(f"{inst.Line} {inst.InstrucKind}, {inst.Rd}, {inst.R1}, {inst.Label}\n")


            elif(inst.InstrucKind == "J" or inst.InstrucKind == "JAL"):
                arquivo.write(f"{inst.Line} {inst.InstrucKind}, {inst.Label}\n")
            
            elif(inst.InstrucKind == "NOP" or inst.InstrucKind == "HLT"):
                arquivo.write(f"{inst.Line} {inst.InstrucKind}\n")


        else:
            arquivo.write(f". {inst.Label}\n")

    return assemList,labelMap,table


if __name__ == '__main__':
    fileName = "outParser.output"
    fileNameTable = "outAnalyze.output" 
    assemblyInstr = assembly(fileName,fileNameTable)
    for inst in assemblyInstr[0]:
        if (inst.LineKind == 0):
            if(inst.InstrucKind == "ADD" or inst.InstrucKind == "SUB" or inst.InstrucKind == "MUL" or inst.InstrucKind == "DIV"
                or inst.InstrucKind == "AND" or inst.InstrucKind == "OR" or inst.InstrucKind == "XOR" or inst.InstrucKind == "SLT"
                or inst.InstrucKind == "SGT" or inst.InstrucKind == "SLET" or inst.InstrucKind == "SGET" or inst.InstrucKind == "SET"):
                print(inst.Line,inst.InstrucKind, inst.Rd, inst.R1, inst.R2)
            
            elif(inst.InstrucKind == "NOT" or inst.InstrucKind == "SR" or inst.InstrucKind == "SL"):
                print(inst.Line,inst.InstrucKind, inst.Rd, inst.R1)

            elif(inst.InstrucKind == "ADDI" or inst.InstrucKind == "SUBI" or inst.InstrucKind == "LOAD" or
                inst.InstrucKind == "STORE"):
                print(inst.Line,inst.InstrucKind, inst.Rd, inst.R1, inst.Im)

            elif(inst.InstrucKind == "JR" or inst.InstrucKind == "IN" or inst.InstrucKind == "OUT"):
                print(inst.Line,inst.InstrucKind, inst.Rd)

            elif(inst.InstrucKind == "BEQ" or inst.InstrucKind == "BNEQ"):
                print(inst.Line,inst.InstrucKind, inst.Rd, inst.R1, inst.Label)
    
            elif(inst.InstrucKind == "J" or inst.InstrucKind == "JAL"):
                print(inst.Line,inst.InstrucKind, inst.Label)
            
            elif(inst.InstrucKind == "NOP" or inst.InstrucKind == "HLT"):
                print(inst.Line,inst.InstrucKind)

        else:
            print(f". {inst.Label}")                        
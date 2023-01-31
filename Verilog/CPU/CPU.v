module Program_counter(
	input clk,									// clock
	input reset,								// reset
	input [31:0] addrin,						// in address
	output reg [31:0] addrout);
	
	always @ (negedge clk) begin
		addrout <= reset ? 31'b0 : addrin;
	end
endmodule

module Mux(A, B, S, Y);
	// Entradas
	input [31:0] A; 
	input [31:0] B; 
	
	input S; // Sinal de controle 
	
	output [31:0] Y; 
	
	assign Y = S ? A : B;
endmodule

module Somador_Padrao(pc, HLT ,pcAtual);
	
	output [31:0] pcAtual;						// Endereco do contador de programa do proximo ciclo
	input [31:0] pc;								// Endereco do contador de programa atual
	input HLT;										// Instrucao final
	
	
	function [31:0] select;
	input [31:0] pc;						
	input HLT;										
	case(HLT)
		1'b0: select = pc + 32'd1; 
		1'b1: select = pc; 
	default: select = 32'd0;
	endcase
	endfunction

	assign pcAtual = select(pc,HLT);
	
endmodule


module ULA(inst, A, B, RD, Resul, isFalse);
	// Entradas
	input [4:0] inst; // Operacao que sera realizada
	input [31:0] A; // Primeiro registrador
	input [31:0] B; // Segundo registrador
	input [31:0] RD; // Registrador RD
	parameter C=1;                         // Deslocamento    


	// Saidas
	output [31:0] Resul; // Resultado da operacao
	output isFalse;

	// Logica sequencial
	function [31:0] select;
	input signed[31:0] A, B, RD;
	input[4:0] inst;
	case(inst)
	// Aritmeticas
	5'b00000: select = A + B; // ADD
	5'b00001: select = A + B; // ADDI
	5'b00010: select = A - B; // SUB
	5'b00011: select = A - B; // SUBI
	5'b00100: select = A * B; // MUL
	5'b00101: select = A / B; // DIV

	// Logicas
	5'b00110: select = A & B; // AND
	5'b00111: select = A ^ B; // XOR
	5'b01000: select = A | B; // OR 
	5'b01001: select = ~A; // NOT

	// Deslocamentos
	5'b01111: select = A >> C; // SR
	5'b10000: select = A << C; // SL

	// Atribuicao 
	5'b10110: select = A + B; // LOAD
	5'b10111: select = A + B; // STORE
	
	// Comparacao
	5'b10100: select = A == RD ? 32'd1 : 32'd0;  //BEQ
	5'b10101: select = A != RD ? 32'd1 : 32'd0;  //BNEQ
	
	5'b01010: select = A < B  ? 32'd1 : 32'd0;  // SLT
	5'b01011: select = A <= B  ? 32'd1 : 32'd0;  // SLET
	5'b01100: select = A > B  ? 32'd1 : 32'd0;  // SGT
	5'b01101: select = A >= B  ? 32'd1 : 32'd0;  // SGET
	5'b01110: select = A == B  ? 32'd1 : 32'd0;  // SET
	
	// Entrada e saida de dados
	5'b11000: select = RD;  // IN
	5'b11001: select = RD;  // OUT

	default: select = 32'd0;
	endcase
	endfunction

	assign isFalse = select(A, B, RD, inst) == 32'd1 ? 1'b1 : 1'b0;
	assign Resul = select(A, B, RD, inst);
endmodule


module Registradores(clock, regWrite, SJal, RJAL, R1, R2,RD, dadosEscrita, leituraR1, leituraR2, leituraRD);
	input [4:0] R1; 
	input [4:0] R2; 
	input [4:0] RD; 
	input [31:0] dadosEscrita, RJAL; // Dado Escrito no Registrador

	output [31:0] leituraR1; // Conteudo de R1
	output [31:0] leituraR2; // Conteudo de R2
	output [31:0] leituraRD; // Conteudo de R2

	input clock;
	input regWrite, SJal; // Sinal de Escrita

	reg [31:0] regs[31:0];
	
	integer i;
	initial begin
		for(i = 0; i < 32 ; i = i + 1)
			regs[i] = 0;
	end
	
	always @ (negedge clock) begin
		regs[RD] <= regWrite ? dadosEscrita : regs[RD];
		
		if( SJal == 1)
			regs[31] = RJAL;
		
	end
		
		assign leituraR1 = regs[R1];
	   assign leituraR2 = regs[R2];
	   assign leituraRD = regs[RD];
endmodule


module Mem_instr
#(parameter DATA_WIDTH=32, parameter ADDR_WIDTH=8)
(
	input [(ADDR_WIDTH-1):0] addr,
	input clk, 
	output reg [(DATA_WIDTH-1):0] q
);

	// Declare the ROM variable
	reg [DATA_WIDTH-1:0] rom[2**ADDR_WIDTH-1:0];

	initial
	begin
		$readmemb("instrucao.txt", rom);
	end

	always @ (posedge clk)
	begin
		q <= rom[addr];
	end

endmodule

module Mem_dados
#(parameter DATA_WIDTH=32, parameter ADDR_WIDTH=8)
(
	input [(DATA_WIDTH-1):0] data,
	input [(ADDR_WIDTH-1):0] read_addr, write_addr,
	input we, read_clock, write_clock,
	output reg [(DATA_WIDTH-1):0] q
);
	
	// Declare the RAM variable
	reg [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH-1:0];
	
	initial 
	begin : INIT
		integer i;
		for(i = 0; i < 2**ADDR_WIDTH; i = i + 1)
			ram[i] = {DATA_WIDTH{1'b0}};
	end 
	
	always @ (negedge write_clock)
	begin
		// Write
		if (we)
			ram[write_addr] <= data;
	end
	
	always @ (posedge read_clock)
	begin
		// Read 
		q <= ram[read_addr];
	end
	
endmodule


// Parte de saida de dados

module instru_out(RD, Out);

input [31:0] RD;
output [31:0] Out;

assign Out = RD;

endmodule


// Terminou parte de saida de dados

//Entrada de dados

module Mux_IN(
	input [31:0] INinstru,
	input [31:0] Regis,
	input clk,									
	input ctrl,								
	output [31:0] addrout);
	
	integer aux;
	
	reg[10:0] count;
	
	initial begin
			count = 0;
	end

	always @ (posedge ctrl) begin
		if (ctrl == 1 && count == 0)begin 
			aux = 0;
			count = count - 5;
		end
		else begin
			aux = count;
			count = count - 1;
		end
		
	end
	
	
	assign addrout = ctrl ? (INinstru + aux) : Regis;
endmodule

//Terminou parte Entrada de dados

// Para rodar na placa FPGA
//module CPU( clk1, resetPC, resetDis, Display1, Display2, Display3, Display4,LEDs, instruIN);
//
//	input clk1, resetPC, resetDis;
//	input [4:0] instruIN;
//	
//	wire clk;
//	DivFreq(clk1,clk);

module CPU( clk, resetPC,out,inst,NotF, resetDis, Display1, Display2, Display3, Display4,LEDs, instruIN);

	input clk, resetPC, resetDis;
	input [4:0] instruIN;
	
	
	wire [4:0]CULA;
	wire SEscritaMem, SEscritaReg,Sddext,Smula,SPC,SHlt, FalseUla,SJal,SIn;
	wire[1:0]SinalM;
	
	wire OutWrite; // Sinal de escrita no display
	wire[31:0] inExt;
	
	
	output [31:0] inst;
	output [31:0]out;
	output NotF;

	output [6:0] Display1, Display2, Display3, Display4, LEDs;
	
	Extensor_Entrada(instruIN, inExt);
	
	SaidaDados(out, OutWrite, clk, resetDis, Display1, Display2, Display3, Display4,LEDs);
	
	Unidade_controle UC(inst[31:27], FalseUla, CULA, SinalM,SEscritaMem,SEscritaReg,Sddext, Smula, Sdes, SPC, SJal, OutWrite, SIn, SHlt,NotF);
	
	datapath data(CULA,SinalM,SEscritaMem,clk,SEscritaReg,Sddext, Smula, Sdes, SPC,resetPC,SHlt,FalseUla,SJal, inExt,SIn, out,inst);
  
  
endmodule


module datapath (ControleUla,SinalMux,SinalEscritaMem,clk,SinalEscritaReg,Sdadoext, Smuxula, Sdesv, SelPC,resetPC,SHlt, FalseUla, SJal, inExt,SIn,saida,Instru);
	
	input[31:0] inExt;
	
	input [4:0]ControleUla;
	input SinalMux;
	input SinalEscritaMem,clk,SinalEscritaReg;
	input Sdadoext, Smuxula, Sdesv, SelPC, SHlt , SJal, SIn , resetPC;
	
	wire [31:0] Dado1, Dado2, DadoRD,Dado2MUX,ResultULA, outMD,outmuxMD;
	wire [31:0] outmuxExte, Exte16, Exte26, DadosIM;
	wire [31:0] AdressPC;
	wire [31:0] Desv, Nextinst;
	wire [31:0] Sumpc, pcSumdesv;
	
	wire [31:0] regWritedata;
	
	output [31:0] saida;
	output[31:0] Instru;
	output FalseUla;
	
	reg[1:0] reduz;
	wire clk_s;
  	always @ (posedge clk) begin
		reduz = reduz + 1;
	end
	assign clk_s = reduz[1];
	
	
	Program_counter Pc(clk_s, resetPC,Nextinst,AdressPC);
	Mem_instr minst(AdressPC , clk_s, Instru);
	
	Registradores Regis(clk_s, SinalEscritaReg , SJal, Sumpc, Instru[21:17], Instru[16:12] , Instru[26:22], regWritedata, Dado1, Dado2, DadoRD);
	
	ULA ula(ControleUla, Dado1, Dado2MUX, DadoRD, ResultULA, FalseUla);     
	
	Mem_dados md( DadoRD , ResultULA, ResultULA, SinalEscritaMem, clk, clk_s, outMD);
	  
	Extensor_bitsB dezesseis(Instru[16:0], Exte16);
	ExtensorBit vinteseis(Instru[26:0], Exte26);
	
	Mux muxexteout(Exte16, Exte26, Sdadoext, DadosIM); // Com o sinal 1 sai dado estendido de 16 bits(multiplex que recebe dos extensores de bits)
	Mux muxULA(Dado2, DadosIM, Smuxula, Dado2MUX); // Com o sinal 0 sai dado que veio do extensor de bits(multiplex entre Banco de regs e Ula)
	Mux muxdesv(DadosIM, DadoRD, Sdesv, Desv);// Com o sinal 1 sai dado estendido
	Mux muxout(ResultULA, outMD, SinalMux, outmuxMD); // Com o sinal 1 sai o resultado da ula, 0 memoria de dados(multiplex depois da memoria de dado)
	
	Mux muxpc(Sumpc , Desv , SelPC, Nextinst);// Com o sinal 0 sai Desv (Resultado que vai para PC)
	
	Mux_IN muxinput(inExt, outmuxMD, clk_s, SIn, regWritedata);
	
	Somador_Padrao SumP(AdressPC, SHlt, Sumpc);  
	
	instru_out t(regWritedata, saida); //saida sempre fica no teste , final regWritedata
endmodule


 

module Unidade_controle(
								
	input [4:0]Instr,
	input FalseUla,

	output reg [4:0]ControleUla,
	output reg SinalMux,
	output reg regSinalEscritaMem,
	output reg SinalEscritaReg,
	output reg Sdadoext, 
	output reg Smuxula, 
	output reg Sdesv, 
	output reg SelPC,
	output reg SJal,
	output reg OutWrite,
	output reg SIn,
	output reg SHlt,
	output reg NotFound
);
	always@*
		
	case(Instr)
	
	// ADD
	5'b00000: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;	
	end
	
	// ADDI
	5'b00001: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b1;
		Smuxula = 1'b0;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end	
	
	// SUB
	5'b00010:
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end
	
	// SUBI
	5'b00011: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b1;
		Smuxula = 1'b0;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end
	
	// MUL
	5'b00100: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end	
	
	// DIV
	5'b00101:
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end	

	// AND
	5'b00110: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end	
	
	// XOR
	5'b00111: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end
	
	// OR
	5'b01000: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end	 
	
	// NOT
	5'b01001: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end
	
	// SLT
	5'b01010:
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end	

	// SLET
	5'b01011: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end	
	
	// SGT
	5'b01100: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end	
	
	// SGET
	5'b01101: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end
	
	// SET
	5'b01110: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end
	
	// SR
	5'b01111:
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end
	
	// SL
	5'b10000: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end
	
	// JR
	5'b10001: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b0;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b0;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end
	
	// J
	5'b10010: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b0;
		Sdadoext= 1'b1;
		Smuxula = 1'b1;
		Sdesv = 1'b1;
		SelPC = 1'b0;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end		
	
	// JAL
	5'b10011: 
	begin	
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b0;
		Sdadoext= 1'b1;
		Smuxula = 1'b1;
		Sdesv = 1'b1;
		SelPC = 1'b0;
		SJal = 1'b1;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end	
	
	// BEQ
	5'b10100: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b0;
		Sdadoext= 1'b1;
		Smuxula = 1'b1;
		Sdesv = 1'b1;
		begin
		
		if(FalseUla)
			SelPC = 1'b0;
		else
			SelPC = 1'b1;
		end
		
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;

	end
	
	// BNEQ
	5'b10101: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b0;
		Sdadoext= 1'b1;
		Smuxula = 1'b1;
		Sdesv = 1'b1;
		begin
		
		if(FalseUla)
			SelPC = 1'b0;
		else
			SelPC = 1'b1;
		end
		
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;

	end
	
	// LOAD
	5'b10110:
	begin
		ControleUla = Instr;
		SinalMux = 1'b0;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b1;
		Smuxula = 1'b0;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end 
	
	// STORE
	5'b10111: 
	begin
		ControleUla = Instr;
		SinalMux = 1'b0;
		regSinalEscritaMem = 1'b1;
		SinalEscritaReg = 1'b0;
		Sdadoext= 1'b1;
		Smuxula = 1'b0;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end
	
	// IN
	5'b11000:
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b1;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b1;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end
	
	// OUT
	5'b11001:
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b0;
		Sdadoext= 1'b1;
		Smuxula = 1'b0;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b1;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end
	
	// NOP
	5'b11010:
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b0;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b0;
		NotFound = 1'b0;
	end
	
	// HLT
	5'b11011:
	begin
		ControleUla = Instr;
		SinalMux = 1'b1;
		regSinalEscritaMem = 1'b0;
		SinalEscritaReg = 1'b0;
		Sdadoext= 1'b0;
		Smuxula = 1'b1;
		Sdesv = 1'b0;
		SelPC = 1'b1;
		SJal = 1'b0;
		OutWrite = 1'b0;
		SIn = 1'b0;
		SHlt = 1'b1;
		NotFound = 1'b0;
	end

	default: NotFound = 1'b1;
	endcase
	
endmodule

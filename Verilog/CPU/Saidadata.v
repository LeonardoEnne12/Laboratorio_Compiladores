module DivisaoCasas(NUM, C, D, U);

	input [9:0] NUM;
	output reg [3:0] C, D, U;
	integer i;
	
	always @(NUM) begin
		C = 4'b0000;
		D = 4'b0000;
		U = 4'b0000;
	
		for(i = 9; i >= 0; i = i - 1) begin
			if(C >= 5)
				C = C + 3;
			if(D >= 5)
				D = D + 3;
			if(U >= 5)
				U = U + 3;
			
			C = C << 1;
			C[0] = D[3];
			D = D << 1;
			D[0] = U[3];
			U = U << 1;
			U[0] = NUM[i];
		end
	end
	
endmodule

module Negativo(NUM,BIN,HEX);

	input [31:0] NUM;
	output reg [31:0] BIN;
	output reg [6:0] HEX;
	integer i;
	
	always@(*)begin
		BIN = NUM;
		if(BIN[31]==1)begin
			for(i=0;i<31;i=i+1)begin
				if(BIN[i]==1)
					BIN[i] = 0;
				else
					BIN[i] = 1;
			end
			BIN = BIN + 1;
			HEX = 7'b1111110;
		end
		else
			HEX = 7'b1111111;
	end

endmodule

module DecodBCD(NUM, HEX);

	input [3:0] NUM;
	output reg [6:0] HEX;
	
	always @(*) begin
		case(NUM)
			4'b0000:HEX = 7'b0000001;
			4'b0001:HEX = 7'b1001111;
			4'b0010:HEX = 7'b0010010;
			4'b0011:HEX = 7'b0000110;
			4'b0100:HEX = 7'b1001100;
			4'b0101:HEX = 7'b0100100;
			4'b0110:HEX = 7'b0100000;
			4'b0111:HEX = 7'b0001111;
			4'b1000:HEX = 7'b0000000;
			4'b1001:HEX = 7'b0000100;
			default:HEX = 7'b1111111;
		endcase
	end
	
endmodule

module SaidaDados(Dado, OutWrite, CLK, Reset, Display1, Display2, Display3, Display4, LEDs);

	input [31:0] Dado;
	wire [3:0] Centena, Dezena, Unidade;
	wire [6:0] HEXc, HEXd, HEXu, HEXn;
	wire [31:0] BIN;
	input OutWrite, CLK, Reset;
	output reg [6:0] Display1, Display2, Display3, Display4;
	output reg [10:0] LEDs;
	
	initial begin
		Display3 = 7'b1111111;
		Display2 = 7'b1111111;
		Display1 = 7'b1111111;
		Display4 = 7'b1111111;
	end

	Negativo Negativo(.NUM(Dado), .BIN(BIN), .HEX(HEXn));
	DivisaoCasas DivisaoCasas(.NUM(BIN[9:0]), .C(Centena), .D(Dezena), .U(Unidade));
	DecodBCD DecodBCD_Centena (.NUM(Centena), .HEX(HEXc));
	DecodBCD DecodBCD_Dezena (.NUM(Dezena), .HEX(HEXd));
	DecodBCD DecodBCD_Unidade (.NUM(Unidade), .HEX(HEXu));
	
	always @(negedge CLK) begin
		if (Reset == 1) begin
			Display3 = 7'b1111111;
			Display2 = 7'b1111111;
			Display1 = 7'b1111111;
			Display4 = 7'b1111111;
			LEDs = 0;
		end
		if (OutWrite == 1) begin
			Display3 = HEXc;
			Display2 = HEXd;
			Display1 = HEXu;
			Display4 = HEXn;
			LEDs = Dado;
		end
	end
	
endmodule
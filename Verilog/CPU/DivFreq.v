module DivFreq(clk,OUT);
input clk;
output reg OUT;
reg[19:0] CONT;
always @(posedge clk)
if(CONT == 19'd100000000) // (CONT == 19'd100000)  (CONT == 19'd100000000) Para o vetor
	begin
		CONT<= 19'd0;
		OUT<= 1;
	end
else 
begin
		CONT<= CONT + 1;
		OUT<= 0;
	end
endmodule

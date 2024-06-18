/* 
	=========================================================================================
	Module name	: funct_generator Register
	Author		: Ana Godoy
	Email		: ana.gm@circuify.com
	Filename	: funct_generator_register.sv
	Type		: SystemVerilog Module
	
	Description	: Registro de 8 bits
	-----------------------------------------------------------------------------------------
    	clocks	        : clk
    	reset	        : async posedge "rst"

	-----------------------------------------------------------------------------------------
	Version		: 1.0
	Date		: Jun 2024
	-----------------------------------------------------------------------------------------
*/

module funct_generator_register #(
	parameter DATA_WIDTH = 8,
				 RESET_VALUE= 0

)(
	input  logic 		        clk,
	input  logic 		        rst,
	input  logic 		        clrh,
	input  logic 		        enh,
	input  logic [DATA_WIDTH - 1:0] d,
	output logic [DATA_WIDTH - 1:0] q	
);

always_ff@(posedge clk, posedge rst) begin
	if(rst)
		data_o<=RESET_VALUE;
	else if(clrh)
		data_o<={DATA_WIDTH{1'b0}};
	else if(enh)
		data_o<=data_i;
	
end

endmodule
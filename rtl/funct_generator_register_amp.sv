/* 
	=========================================================================================
	Module name	: funct_generator Register
	Author		: Ana Godoy
	Email			: ana.gm@circuify.com
	Filename		: funct_generator_register.sv
	Type			: SystemVerilog Module
	
	Description	: Registro de 8 bits
	-----------------------------------------------------------------------------------------
		clocks	: clk
		reset		: async posedge "rst"

	-----------------------------------------------------------------------------------------
	Version		: 1.0
	Date			: 19 Jun 2023
	-----------------------------------------------------------------------------------------
*/

module funct_generator_register_amp #(
	parameter DATA_WIDTH = 8,
	parameter RESET_VALUE= 8'h10

)(
	input  logic 			clk,
	input  logic 			rst,
	input  logic 			clrh,
	input  logic 			enh,
	input  logic [3:4-DATA_WIDTH] 	d,
	output logic [3:4-DATA_WIDTH] 	q 	
);

always_ff@(posedge clk, posedge rst) begin
	if(rst)
		q <= RESET_VALUE;
	else if(clrh)
		q <= RESET_VALUE;
	else if(enh)
		q <= d;
	
end

endmodule

/* 
	=========================================================================================
	Module name	: funct_generator Multiplicator
	Author		: Ana Godoy
	Email		: ana.gm@circuify.com
	Filename	: funct_generator_multi.sv
	Type		: Modulo SystemVerilog
	
	Description	: Multiplicador 2 entradas con enable
	-----------------------------------------------------------------------------------------
	Version		: 1.0
	Date		: Jun 2024
	-----------------------------------------------------------------------------------------
*/

module funct_generator_multi #(
	parameter DATA_WIDTH=8,
				DATA_WIDTH_OUT=16

)(
	//INPUTS
	input  logic 				enh, 
	input  logic signed[0:1-DATA_WIDTH]	a_i,
	input  logic signed[3:4-DATA_WIDTH]	b_i,
	
	//OUTPUTS
	output logic signed [3:4-DATA_WIDTH_OUT] data_o
);


always_comb begin
	if(enh) begin
	    data_o = (a_i * b_i);
	end
end

endmodule


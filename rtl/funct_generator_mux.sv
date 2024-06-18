/* 
	=========================================================================================
	Module name	: funct_generator multiplexor
	Author		: Ana Godoy
	Email		: ana.gm@circuify.com
	Filename	: funct_generator_multi.sv
	Type		: Modulo SystemVerilog
	
	Description	: Multiplexor
	-----------------------------------------------------------------------------------------
	Version		: 1.0
	Date		: Jun 2024
	-----------------------------------------------------------------------------------------
*/

module funct_generator_mux #(
	parameter DATA_WIDTH=8,
	parameter DATA_WIDTH_OUT=16

)(
	//INPUTS
	input  logic       [1:0] 		sel_i, 
	input  logic signed[3:4-DATA_WIDTH_OUT]	data_0_i,
	input  logic signed[3:4-DATA_WIDTH_OUT]	data_1_i,
	input  logic signed[3:4-DATA_WIDTH_OUT]	data_1_i,
	input  logic signed[3:4-DATA_WIDTH_OUT]	data_3_i,
	//OUTPUTS
	output logic signed [3:4-DATA_WIDTH_OUT] data_o
);


always_comb begin
    case(sel_i)
        0: data_o = data_0_i;
        1: data_o = data_1_i;
        2: data_o = data_2_i;
        3: data_o = data_3_i;
    endcase
end

endmodule


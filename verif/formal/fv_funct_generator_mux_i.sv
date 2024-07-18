import gen_fifo_defines_pkg::*;

module fv_funct_generator_mux_i(
	input  logic       [1:0] 	    	sel_i, 
	input  logic                 	    	enh, 
	input  logic signed[`DATA_WIDTH-1 : 0] 	data_0_i,
	input  logic signed[`DATA_WIDTH-1 : 0] 	data_1_i,
	input  logic signed[`DATA_WIDTH-1 : 0] 	data_2_i,
	input  logic signed[`DATA_WIDTH-1 : 0] 	data_3_i,
	input logic signed [`DATA_WIDTH-1 : 0] 	data_o
);
	`define CLK_PATH fv_generator_inst.clk

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////
	
	// 1) Assume that if ehn is not active data_o value is 0.
	assume property (@(posedge `CLK_PATH) (!enh) |-> (data_o == '0));

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures data_o matches data_0_i when sel_i is 0 and enh is active.
	data_o_is_data_0_i: assert property (@(posedge `CLK_PATH) (enh && (sel_i == 2'b00)) |-> data_o == data_0_i) $info("Assetion pass data_o_is_data_0_i");
	else $error(" Asserion fail data_o_is_data_0_i");
	
	// 2) The property assures data_o matches data_1_i when sel_i is 1 and enh is active.
	data_o_is_data_1_i: assert property (@(posedge `CLK_PATH) (enh && (sel_i == 2'b01)) |-> data_o == data_1_i) $info("Assetion pass data_o_is_data_1_i");
	else $error(" Asserion fail data_o_is_data_1_i");

	// 3) The property assures data_o matches data_2_i when sel_i is 2 and enh is active.
	data_o_is_data_2_i: assert property (@(posedge `CLK_PATH) (enh && (sel_i == 2'b10)) |-> data_o == data_2_i) $info("Assetion pass data_o_is_data_2_i");
	else $error(" Asserion fail data_o_is_data_2_i");

	// 4) The property assures data_o matches data_3_i when sel_i is 3 and enh is active.
	data_o_is_data_3_i: assert property (@(posedge `CLK_PATH) (enh && (sel_i == 2'b11)) |-> data_o == data_3_i) $info("Assetion pass data_o_is_data_3_i");
	else $error(" Asserion fail data_o_is_data_3_i");
 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
	
	// 1) Covers when enable is active and selector value is 0.
	cover_enh_1_sel_0: cover property (@(posedge `CLK_PATH) enh && (sel_i == 2'b00));
	
	// 2) Covers when enable is active and selector value is 1.
	cover_enh_1_sel_1: cover property (@(posedge `CLK_PATH) enh && (sel_i == 2'b01));

	// 3) Covers when enable is active and selector value is 2.
	cover_enh_1_sel_2: cover property (@(posedge `CLK_PATH) enh && (sel_i == 2'b10));

	// 4) Covers when enable is active and selector value is 3.
	cover_enh_1_sel_3: cover property (@(posedge `CLK_PATH) enh && (sel_i == 2'b11));

endmodule

bind funct_generator_mux fv_funct_generator_mux_i fv_generator_mux_i_inst(.*);

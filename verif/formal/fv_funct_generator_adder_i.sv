import gen_fifo_defines_pkg::*;

module fv_funct_generator_adder_i (
	input  logic 	    		clrh,
	input  logic 	    		enh,
	input  logic [`LUT_ADDR-1:0]  	data_a_i,
	input  logic [`LUT_ADDR-1:0]  	data_b_i,
	input  logic [`LUT_ADDR-1:0] 	data_c_i,
	input  logic [`LUT_ADDR-1:0]	data_o 
);
    `define CLK_PATH fv_generator_inst.clk
///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	// 1) Assume enable and clear signals are not active simultaneously.
 	 enh_and_clrh_notactive_same: assume property (@(posedge `CLK_PATH) !(enh && clrh));

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	// 1) The property assures that when clrh is high, the output data_o is set to zero.
	clrh_on_data_o_zero: assert property (@(posedge `CLK_PATH) (clrh) |-> (data_o == '0)) $info("Assetion pass clrh_on_data_o_zero");
	else $error(" Asserion fail clrh_on_data_o_zero");
	
	// 2) The property assures that when enh is 1 and clrh is 0 data_o is the sum of data_a_i, data_b_i, and data_c_i. //DATA_WIDTH change for LUT_ADDR
	enh_on_data_o_increment: assert property (@(posedge `CLK_PATH) (enh && (!clrh)) |-> (data_o == (data_a_i + data_b_i + data_c_i))) $info("Assetion pass enh_on_data_o_increment");
 	else $error(" Asserion fail enh_on_data_o_increment");
	
	// 3) The property assures that when enh is low and clrh is low, the output data_o remains unchanged. //changing $past for $stable and |=> for |->
	data_o_stability_when_disabled: assert property (@(posedge `CLK_PATH) ((!enh) && (!clrh)) |-> ($stable(data_o))) $info("Assetion pass data_o_stability_when_disabled"); 
   	else $error(" Asserion fail data_o_stability_when_disabled");
 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 1) Cover that is data_o is 0 when clrh is asserted.
  	clrh_clears_output: cover property (@(posedge `CLK_PATH) (clrh && data_o == 0));
	
	// 2) Cover the scenario where enh is asserted and the adder performs the addition operation.
      	enh_add_operation: cover property (@(posedge `CLK_PATH) (enh && (!clrh) && (data_o == (data_a_i + data_b_i + data_c_i))));

endmodule

bind funct_generator_adder fv_funct_generator_adder_i fv_generator_adder_i_inst(.*);

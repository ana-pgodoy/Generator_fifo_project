import gen_fifo_defines_pkg::*;

module fv_funct_generator_multi (
	input  logic 				enh, 
	input  logic signed[`DATA_WIDTH-1:0]	a_i,
	input  logic signed[`DATA_WIDTH-1:0]	b_i,
	input logic signed [(`DATA_WIDTH*2)-1:0] data_o
);
	`define CLK_PATH fv_generator_inst.clk
	`define RST_PATH fv_generator_inst.rst
	bit flag;

  	always @(posedge `CLK_PATH) begin
      	if (`RST_PATH == 1'b1)
        	flag <= 1'b0;
      	else 
        	flag <=1'b1;
  	end

///////////////////////////////////////////////////// Assumptions /////////////////////////////////////////////

	//1)

///////////////////////////////////////////////////// Assertions /////////////////////////////////////////////

	//1) The property assures when enh is active the multiplication operation performs correcty
      	multiplication_correct: assert property (@(posedge `CLK_PATH) (enh) |-> (data_o == (a_i * b_i))) $info("Assetion pas smultiplication_correct");
	else $error(" Asserion fail multiplication_correct");
      	
	// 2) The property assures that when enh is low the output data_o remains unchanged. //changing $past for $stable and |=> for |-> and adding flag
      	data_o_stability_when_enh_0: assert property (@(posedge `CLK_PATH) ((!enh) && flag) |-> ($stable(data_o))) $info("Assetion pass data_o_stability_when_enh_0");
	else $error(" Asserion fail data_o_stability_when_enh_0");

 
///////////////////////////////////////////////////// Covers /////////////////////////////////////////////////////
   	
	// 1) Cover property for the multiplication scenario.
	multi_cover: cover property (@(posedge `CLK_PATH) ((enh) && (data_o == (a_i * b_i))));

endmodule

bind funct_generator_multi fv_funct_generator_multi_i fv_generator_multi_i_inst(.*);

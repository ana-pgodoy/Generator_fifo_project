
/******************************
*** gen_fifo_defines_pkg    ***
*** Author: Ana Godoy       ***
*** Date: Jun 2024	    ***
*****************************/

package gen_fifo_defines_pkg;

  `define DATA_WIDTH    6'h20
  `define INT_BITS      3'h4        
  `define LUT_ADDR      4'h8
  `define RESET_VALUE   0
  `define RESET_AMP     32'h10000000
  `define COS_FILE      "../../rtl/cos.txt"
  `define SIN_FILE      "../../rtl/sin.txt"
  `define TRIAN_FILE    "../../rtl/triangular.txt"
  `define SQUA_FILE     "../../rtl/square.txt"
endpackage

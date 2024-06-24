clc; close all; clear all; %%limpiar variables, pantalla y figuras
fmax = 1;  Fs = fmax*255;
Time = 0:1/Fs:1; %%
amplitud=1;

%signals
cosine_s = amplitud*cos(2*pi*fmax*Time);
sine_s = amplitud*sin(2*pi*fmax*Time);
triangular_s = amplitud*sawtooth(2*pi*fmax*Time+1.561, 1/2);
square_s = amplitud*square(2*pi*fmax*Time);

%Analysis 
WordLength = 32;
QI_sinusoid = 4; %%Integers
QF_sinusoid = WordLength-QI_sinusoid; %%Fraction

signal_sin_dec = fi(sine_s,1,WordLength,QF_sinusoid)
signal_sin_bin = bin(fi(sine_s,1,WordLength,QF_sinusoid))
fileSINE = fopen('sin_dec.txt','w');
fprintf(fileSINE,'%1.4f \n',signal_sin_dec);

signal_cos_dec = fi(cosine_s,1,WordLength,QF_sinusoid)
signal_cos_bin = bin(fi(cosine_s,1,WordLength,QF_sinusoid))
fileCOSINE = fopen('cos_dec.txt','w');
fprintf(fileCOSINE,'%1.4f \n',signal_cos_dec);

signal_trian_dec = fi(triangular_s,1,WordLength,QF_sinusoid)
signal_trian_bin = bin(fi(triangular_s,1,WordLength,QF_sinusoid));
fileTRIAN = fopen('triangular_dec.txt','w');
fprintf(fileTRIAN,'%1.4f \n',signal_trian_dec);

signal_squa_dec = fi(square_s,1,WordLength,QF_sinusoid)
signal_squa_bin = bin(fi(square_s,1,WordLength,QF_sinusoid));
fileSQUA = fopen('square_dec.txt','w');
fprintf(fileSQUA,'%1.4f \n',signal_squa_dec);

%Graphics
figure; hold on;

plot(Time,cosine_s,'r');
plot(Time,sine_s,'g');
plot(Time,square_s,'b');
plot(Time,triangular_s,'m');

yline(0, '-.c');

legend('cosine','sine', 'square','triangular');
title('Funtions');
xlabel('Periods *1 = 256 clock cycles*');
ylabel('Values Amplitude = 1'); 



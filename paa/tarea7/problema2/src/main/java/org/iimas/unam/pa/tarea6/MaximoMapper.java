package org.iimas.unam.pa.tarea6;

import java.io.IOException;
import org.apache.hadoop.io.*;
import org.apache.hadoop.mapreduce.Mapper;

public class MaximoMapper
    extends Mapper<LongWritable, Text, Text, DoubleWritable> {
    protected void map(LongWritable key, Text linea, Context context)
        throws IOException, InterruptedException 
        {
            String[] datos = linea.toString().split (",");
            try{
                double x=Double.parseDouble(datos[2]);     
                context.write(new Text ("max"),
                              new DoubleWritable(x));
            }catch(NumberFormatException nfe){
            }
        }
}

package org.iimas.unam.pa.tarea6;

import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import org.apache.hadoop.io.DoubleWritable;
import org.apache.hadoop.io.IntWritable;
import org.apache.hadoop.io.LongWritable;
import org.apache.hadoop.io.NullWritable;
import org.apache.hadoop.io.Text;
import org.apache.hadoop.mapreduce.*;

public class MaximoReducer
extends Reducer<Text, DoubleWritable, Text, DoubleWritable> {
	@Override
	public void reduce(Text key, Iterable<DoubleWritable> values, Context context)
			throws IOException, InterruptedException 
      {
          System.out.println(context.getClass().getName());
          double max = Double.MIN_VALUE;
          for (DoubleWritable value : values) {
              if (value.get() > max) {
                  max = value.get();
              }
          }
          context.write(key, new DoubleWritable(max));
      }
}

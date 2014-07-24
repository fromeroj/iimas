package org.iimas.unam.pa.tarea6;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.apache.hadoop.io.*;
import org.apache.hadoop.mrunit.mapreduce.MapDriver;
import org.apache.hadoop.mrunit.mapreduce.ReduceDriver;
import org.apache.hadoop.conf.Configuration;
import org.apache.hadoop.fs.FileSystem;
import org.apache.hadoop.fs.Path;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

/**
 * Unit test for simple App.
 */
public class AppTest 
extends TestCase
{
	MapDriver<LongWritable, Text, Text, DoubleWritable> mapDriver;
	ReduceDriver<Text, DoubleWritable, Text, DoubleWritable> reduceDriver;
	/**
	 * Create the test case
	 *
	 * @param testName name of the test case
	 */
	public AppTest( String testName )
	{
		super( testName );
		MaximoMapper mapper  = new MaximoMapper();
		mapDriver = MapDriver.newMapDriver(mapper);

		MaximoReducer reducer = new MaximoReducer();
		reduceDriver = ReduceDriver.newReduceDriver(reducer);
	}

	/**
	 * @return the suite of tests being tested
	 */
	public static Test suite()
	{
		return new TestSuite( AppTest.class );
	}

	/**
	 * Rigourous Test :-)
	 */
	public void testApp()
	{
		assertTrue( true );
	}    

	public void testMapper() throws IOException, InterruptedException {
		long llave = 1;
		double valor = 2.13;
		Text texto = new Text("436650.1494750933,853230.9443486946,605966.3543574564,325617.7004387456,684831.1360391678");

		mapDriver.withInput(new LongWritable(llave), texto);
		mapDriver.withOutput(new Text("max"), new DoubleWritable(605966.3543574564));
		mapDriver.runTest();
	}


	public void testReducer () throws IOException,
	InterruptedException {
		Text llave = new Text("max");
		List<DoubleWritable> values = new ArrayList<DoubleWritable>();
		values.add(new DoubleWritable(1.2));
		values.add(new DoubleWritable(1.7));
		values.add(new DoubleWritable(2.1));
		// max Temperatura
		reduceDriver.withInput(llave, values);
		reduceDriver.withOutput(llave, new DoubleWritable(2.1));
		reduceDriver.runTest();
	}

	public void testConf () throws Exception {
		Configuration conf = new Configuration();
		conf.set("fs.default.name", "file:///");
		conf.set("mapred.job.tracker", "local");
		Path input = new Path("./datos_cols.csv");
		Path output = new Path("salida");

		FileSystem fs = FileSystem.getLocal(conf);
		fs.delete(output, true); // borra el directorio de salida

		Problema1 driver = new Problema1();
		driver.setConf(conf);
		int exitCode = driver.run(new String[] {
				input.toString(), output.toString() });
		assertEquals(exitCode, 0);
	}
}
